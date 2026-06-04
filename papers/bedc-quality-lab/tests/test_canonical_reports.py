import json
import os
from pathlib import Path
import sys
import types

import pytest

from scripts import run_formal_hardening_report as formal_hardening
from scripts import run_claim_verdict_demo as claim_verdict_demo
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map


HG_P_CORE = {
    "mixing-family-sweep",
    "anisotropic-ou-sweep",
    "gap-head-on-h",
    "gap-head-discovery",
    "gap-head-ablation",
    "gap-head-threshold-frontier",
    "gap-head-transfer-atlas",
    "gap-head-attribution-capsule",
    "certificate-guided-training",
    "certificate-guided-discovery",
    "sigreg-training-proxy",
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
                "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
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
            "scope": {"not_claimed": ["fixture nonclaim"]},
            "claim_gate": {
                "status": "fixture",
                "audit_improvement_tradeoff": spec.name == "certificate-guided-training",
                "training_audit_improvement_tradeoff": spec.name == "certificate-guided-discovery",
            },
            "paired_seed_protocol": {"status": "fixture"},
            "arm_protocol": {"status": "fixture"},
            "arm_summaries": {"status": "fixture"},
            "grid_summary": {"record_count": 1, "by_arm": {"constraint_lagrangian": {"record_count": 1}}},
            "grid_metrics_artifact": "reports/runs/certificate-guided-constraint-training/grid_metrics.jsonl",
            "grid_summary_artifact": "reports/runs/certificate-guided-constraint-training/grid_summary.jsonl",
            "raw_metrics_artifact": "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl",
            "raw_metrics_record_count": 56,
            "raw_grid_record_count": 3024,
            "main_claim_status": "fixture status",
            "final_main_claim_status": "fixture status",
            "hardgate": {"status": "pass"},
            "failed_gate": None,
            "verdict": "accepted",
            "discovery_level": "D0",
            "metrics": {
                "delta_debt": -0.25,
                "delta_benefit": -0.10,
                "delta_cost": 0.0,
                "delta_quality_q": 0.15,
                "UER": {"mean": 0.1},
                "FalseLedgerRate": {"mean": 0.05},
                "positive_quality_gate": False,
                "positive_discovery": False,
                "audit_improvement_tradeoff": spec.name == "certificate-guided-training",
                "ParetoDominance": False,
            },
            "claim_capsule": {
                "schema_id": "bedc.quality.claim_capsule",
                "terminal_verdict": "DN(audit-improvement-tradeoff)",
                "failed_gate": "audit-improvement-tradeoff" if spec.name == "certificate-guided-training" else None,
            },
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
            "surface_registry": [{"surface_id": "S0"}],
            "surfaces": [{"surface_id": "S0"}],
            "boundary_ledger": [],
            "hardgate_evidence": {"A2-HG5": {"status": "pass"}},
            "multi_surface_d5_o": {"decision": "pass", "discovery_level": "D5-O", "pass_surface_count": 3},
            "prior_observation_packet": {
                "status": "prior_observation",
                "counts_as_a2_hg_pass_evidence": False,
                "packet_pointer": "$.prior_observation_packet",
                "observations": {},
            },
            "run_id": "fixture-run",
            "run_artifacts": {
                "claim_capsule": "reports/runs/fixture/claim_capsule.json",
                "raw_metrics": "reports/runs/fixture/raw_metrics.jsonl",
                "summary": "reports/runs/fixture/summary.json",
                "report": "reports/runs/fixture/report.md",
            },
            "objective": {
                "required_rows": ["fixture"],
                "id": "sigreg_sliced_cf_training_proxy",
                "loss": "(1-lambda)*alignment + lambda*sigreg_sliced_cf",
            },
            "arm_protocol": {
                "exact_arm_count": 4,
                "arms": [
                    "covariance_proxy_current",
                    "true_sigreg_sliced_cf",
                    "vicreg_like_covariance",
                    "alignment_only",
                ],
            },
            "d1_evidence": {
                "debt_delta": -1.0,
                "d1_hardgates": {
                    "D1-HG1": {"status": "pass"},
                    "D1-HG2": {"status": "pass"},
                    "D1-HG3": {"status": "pass"},
                    "D1-HG4": {"status": "pass"},
                    "D1-HG5": {"status": "pass"},
                },
            },
            "positive_claim": {"text": "fixture D1 SIGReg training proxy", "scope": "fixture", "level": "D1"},
            "claim_capsule_ref": {
                "artifact": "reports/runs/fixture/claim_capsule.json",
                "pointer": "$",
            },
            "result_snapshot_ref": {
                "artifact": "reports/runs/fixture/result_snapshot.json",
                "pointer": "$",
            },
            "full_lejepa_boundary": {
                "claim": False,
                "required_to_claim": ["2D mixings", "grid", "distribution sweep"],
            },
            "what_was_learned": "fixture",
            "failed_gate": None,
            "forbidden_claim_term_audit": {"status": "pass", "hits": []},
        }
    )
    if spec.name == "gap-head-transfer-atlas":
        payload["config"] = {"control_arm": "matched_random_gap_head"}
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
    if spec.name == "gap-head-attribution-capsule":
        payload["cost_protocol_pointer"] = "$.source_artifacts.cost_protocol"
        payload["source_artifacts"]["cost_protocol"] = {
            "status": "recorded",
            "surface_protocol": {"surface_helper": "fixture-surface-helper"},
            "control_protocol": {"matched_random_helper": "fixture-control-helper"},
        }
        payload["d5_o"] = {"status": "ready"}
        payload["d5_m"] = {"status": "blocked", "passed": False, "failed_gate": "A4-HG5"}
        payload["residualized_attribution"] = {"status": "pass"}
        payload["score_margin_causal_evidence"] = {"channel_classification": "score_margin_sufficient"}
        payload["a4_hardgates"] = {
            "status": "fail",
            "gates": {"A4-HG5": {"status": "fail"}},
        }
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
    sidecar_path = tmp_path / canonical_module.GAP_HEAD_MECHANISM_NAMECERT_JSON_ARTIFACT
    sidecar_path.parent.mkdir(parents=True, exist_ok=True)
    sidecar_path.write_text(
        json.dumps(
            {
                "artifact_id": canonical_module.GAP_HEAD_MECHANISM_NAMECERT_ARTIFACT_ID,
                "ledger_policy": {"mechanism_closure_debt": "open"},
                "closure_status": {"mechanism_spec": "partial"},
                "mechanism_spec": {
                    "candidate_mechanism": "probe-margin-channel",
                    "full_vs_score_plus_margin": "not separated",
                    "a1_failed_gate": "A1-HG3",
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )


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


def _read_committed_claim_verdicts():
    path = canonical.ROOT / canonical.CLAIM_VERDICTS_JSONL_ARTIFACT
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


def _normalized_index_report(report):
    item = dict(report)
    item["duration_seconds"] = 0.0
    item["producer_status"] = "reused"
    return item


def _canonical_bundle_payloads_for_timestamps(*, index_timestamp, discovery_timestamp):
    committed_index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    generated_claims = claim_verdict_demo.compile_claim_verdicts(canonical.ROOT, generated_at=index_timestamp)
    generated_index = canonical._index(
        [_normalized_index_report(report) for report in committed_index["reports"]],
        generated_at=index_timestamp,
        claim_verdict_rows=generated_claims,
    )
    generated_discovery = discovery_map.build_discovery_map(
        generated_at=discovery_timestamp,
        root=canonical.ROOT,
        canonical_reports=canonical.CANONICAL_REPORTS,
    )
    return generated_index, generated_discovery, generated_claims


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
        "gap-head-transfer-atlas",
        "gap-head-attribution-capsule",
        "nongaussian-distribution-sweep",
        "certificate-guided-training",
        "certificate-guided-discovery",
        "sigreg-training-proxy",
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


def test_committed_canonical_bundle_covers_every_registered_report():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    discovery_payload = json.loads((canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()
    registered = {spec.name: spec for spec in canonical.CANONICAL_REPORTS}

    index_reports = {row["name"]: row for row in index_payload["reports"]}
    discovery_rows = {row["report"]: row for row in discovery_payload["rows"]}
    claim_ids = {row["claim_id"] for row in claim_rows}

    assert set(index_reports) == set(registered)
    assert set(registered).issubset(discovery_rows)
    assert {f"claim:{name}" for name in registered}.issubset(claim_ids)
    for name, spec in registered.items():
        assert index_reports[name]["json_artifact"] == spec.json_artifact
        assert discovery_rows[name]["json_artifact"] == spec.json_artifact
        assert (canonical.ROOT / spec.json_artifact).exists()
        assert (canonical.ROOT / spec.markdown_artifact).exists()


def test_committed_canonical_bundle_matches_generation_chain():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    discovery_payload = json.loads((canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()
    generated_index, generated_discovery, generated_claims = _canonical_bundle_payloads_for_timestamps(
        index_timestamp=index_payload["generated_at"],
        discovery_timestamp=discovery_payload["generated_at"],
    )

    assert index_payload == generated_index
    assert discovery_payload == generated_discovery
    assert claim_rows == generated_claims


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


def test_canonical_reports_manifest_includes_gap_head_transfer_atlas():
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]

    assert spec.command == ("python3", "scripts/run_gap_head_transfer_atlas.py")
    assert spec.json_artifact == "reports/canonical/gap_head_transfer_atlas.json"
    assert spec.markdown_artifact == "reports/canonical/gap_head_transfer_atlas.md"
    assert {
        "surface_registry",
        "prior_observation_packet",
        "surfaces",
        "boundary_ledger",
        "hardgate_evidence",
        "multi_surface_d5_o",
        "forbidden_claim_term_audit",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.not_claimed"
    assert spec.cost_pointer == "$.source_artifacts.metric_helper"
    assert spec.positive_claim_pointer == "$.multi_surface_d5_o"
    assert spec.control_pointer == "$.config.control_arm"


def test_canonical_reports_manifest_includes_gap_head_attribution_capsule():
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]

    assert spec.command == ("python3", "scripts/run_gap_head_attribution_capsule.py")
    assert spec.json_artifact == "reports/canonical/gap_head_attribution_capsule.json"
    assert spec.markdown_artifact == "reports/canonical/gap_head_attribution_capsule.md"
    assert {
        "schema_id",
        "source_issue",
        "artifact_id",
        "run_id",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "hardgates",
        "residualized_attribution",
        "score_margin_causal_evidence",
        "a4_hardgates",
        "claim_capsule_hardgates",
        "forbidden_column_audit",
        "source_artifacts",
        "aggregate",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.scope.not_claimed"
    assert spec.cost_pointer == "$.cost_protocol_pointer"
    assert spec.control_pointer == "$.control_pointer"
    assert "residualized-attribution" not in {item.name for item in canonical.CANONICAL_REPORTS}


def test_canonical_index_uses_pointer_only_mechanism_namecert_sidecar(tmp_path, monkeypatch):
    sidecar = tmp_path / canonical.GAP_HEAD_MECHANISM_NAMECERT_JSON_ARTIFACT
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "artifact_id": canonical.GAP_HEAD_MECHANISM_NAMECERT_ARTIFACT_ID,
                "mechanism_spec": {"candidate_mechanism": "probe-margin-channel"},
                "ledger_policy": {"mechanism_closure_debt": "open"},
                "closure_status": {"mechanism_spec": "partial"},
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    section = canonical._gap_head_mechanism_namecert_index_section()
    payload = canonical._index([])
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-mechanism-namecert" not in names
    assert section["artifact_id"] == canonical.GAP_HEAD_MECHANISM_NAMECERT_ARTIFACT_ID
    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert section["ledger_policy_pointer"] == "$.ledger_policy.mechanism_closure_debt"
    assert section["closure_status_pointer"] == "$.closure_status.mechanism_spec"
    assert section["candidate_mechanism"] == "probe-margin-channel"
    assert payload["gap_head_mechanism_namecert"]["mechanism_closure_debt"] == "open"
    absent_key = "gap_head_mechanism_" + "attribution"
    assert absent_key not in payload
    assert "Gap-head mechanism NameCert candidate" in markdown


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
    training_discipline = canonical._discipline(training)

    assert training.command == ("python3", "scripts/run_certificate_guided_constraint_training.py")
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
        "grid_summary",
        "grid_metrics_artifact",
        "grid_summary_artifact",
        "raw_metrics_artifact",
        "metrics",
        "claim_gate",
        "hardgate",
        "failed_gate",
        "verdict",
        "discovery_level",
        "not_claimed",
        "claim_capsule",
    }.issubset(set(training.required_json_keys))
    assert training.bundle_role == "hg_p_core"
    assert training_discipline["evidence_pointer"] == "$.arm_protocol.compat_roles.after"
    assert training_discipline["evidence_label"] == "constraint_lagrangian"
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


def test_canonical_reports_manifest_includes_sigreg_training_proxy():
    spec = canonical._specs_by_name()["sigreg-training-proxy"]

    assert spec.command == ("python3", "scripts/run_sigreg_training_proxy.py")
    assert spec.json_artifact == "reports/canonical/sigreg-training-proxy.json"
    assert spec.markdown_artifact == "reports/canonical/sigreg-training-proxy.md"
    assert {
        "run_artifacts",
        "objective",
        "arm_protocol",
        "d1_evidence",
        "positive_claim",
        "claim_capsule_ref",
        "result_snapshot_ref",
        "full_lejepa_boundary",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.arm_protocol"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.control_pointer is None
    assert spec.no_control_rationale_pointer == "$.full_lejepa_boundary"


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


def test_generated_index_contains_outline_claims_nonclaims_and_honest_boundary_sections(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    for spec in canonical.CANONICAL_REPORTS:
        json_path = canonical._artifact_path(spec.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    transfer_path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
    transfer_path.parent.mkdir(parents=True, exist_ok=True)
    transfer_path.write_text(
        json.dumps(
            {
                "dimension_mismatch_debt_transfer": {
                    "status": "pass",
                    "base_level": "D4",
                    "anti_triviality_status": "scale_leakage_detected",
                    "effective_level": "DN",
                    "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
                    "terminal_verdict": "negative_discovery",
                    "hypothesis": "fixture hypothesis",
                    "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
                    "what_was_learned": "fixture learned",
                    "discovery_level": "DN",
                    "scope": "fixture scope",
                }
            }
        )
        + "\n",
        encoding="utf-8",
    )
    robustness_path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT
    robustness_path.write_text(json.dumps({"audit_status": "pass"}) + "\n", encoding="utf-8")
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 4, "required": 4, "gap_count": 0},
    )
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
            "claim_capsule",
            "formal_hardening",
        }.issubset(payload)
    assert set(payload["paper_outline"]["core_reports"]) == HG_P_CORE
    assert payload["negative_witnesses"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:discovery-negative-witnesses",
        "json_artifact": "reports/canonical/discovery_negative_witnesses.json",
        "expected_kind_count": 8,
        "schema_role": "bedc-gap-witness-ledger",
        "required_fields": [
            "bedc_gap_field",
            "violated_principle",
            "required_ledger_row",
            "demotion",
            "regression_test",
        ],
    }
    assert payload["claim_verdicts"]["status"] == "pointer-only"
    assert payload["claim_verdicts"]["artifact_id"] == "bedc-quality-lab:claim-verdicts"
    assert payload["claim_verdicts"]["jsonl_artifact"] == "reports/canonical/claim_verdicts.jsonl"
    assert isinstance(payload["claim_verdicts"]["row_count"], int)
    assert payload["claim_capsule"]["status"] == "pointer-only"
    assert payload["claim_capsule"]["artifact_id"] == "bedc-quality-lab:claim-capsule"
    assert payload["claim_capsule"]["schema_id"] == "bedc.quality.claim_capsule"
    assert payload["claim_capsule"]["json_artifact"] == "reports/canonical/claim_capsule.json"
    assert payload["claim_capsule"]["effective_level"] == "DN"
    assert payload["claim_capsule"]["terminal_verdict"] == "negative_discovery"
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
    assert "Claim capsule" in markdown
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


def test_run_spec_can_reuse_existing_artifacts_without_producer(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    def unexpected_producer(_spec):
        raise AssertionError("producer should not run")

    monkeypatch.setattr(canonical, "_run_producer", unexpected_producer)

    result = canonical._run_spec(spec, reuse_existing=True)

    assert result["status"] == "pass"
    assert result["producer_status"] == "reused"
    assert result["validation"]["status"] == "pass"


def test_run_spec_force_path_runs_producer_for_existing_artifacts(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")
    calls = []

    monkeypatch.setattr(canonical, "_run_producer", lambda called: calls.append(called.name))

    result = canonical._run_spec(spec, reuse_existing=False)

    assert calls == ["mixing-family-sweep"]
    assert result["producer_status"] == "completed"


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
        payload = _payload_for_spec(spec)
        if spec.name == "gap-head-transfer-atlas":
            payload["multi_surface_d5_o"] = {
                "decision": "pass",
                "discovery_level": "D5-O",
                "pass_surface_count": 3,
            }
        json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
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
        payload = _payload_for_spec(spec)
        if spec.name == "gap-head-transfer-atlas":
            payload["multi_surface_d5_o"] = {
                "decision": "pass",
                "discovery_level": "D5-O",
                "pass_surface_count": 3,
            }
        json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["artifact_id"] == "bedc-quality-lab:discovery-map"
    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert "Discovery map" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")


def test_gap_head_transfer_atlas_index_matches_discovery_map_row(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        payload = _payload_for_spec(spec)
        if spec.name == "gap-head-transfer-atlas":
            payload["multi_surface_d5_o"] = {
                "decision": "pass",
                "discovery_level": "D5-O",
                "pass_surface_count": 3,
            }
        json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    discovery_payload = json.loads(
        (canonical.CANONICAL_DIR / "discovery_map.json").read_text(encoding="utf-8")
    )
    atlas_row = next(row for row in discovery_payload["rows"] if row["report"] == "gap-head-transfer-atlas")
    negative_reports = json.loads(
        (canonical.CANONICAL_DIR / "negative_discovery_reports.json").read_text(encoding="utf-8")
    )
    owner_index = int(
        atlas_row["negative_report_pointer"]
        .removeprefix("reports/canonical/negative_discovery_reports.json:$.rows[")
        .removesuffix("]")
    )
    atlas_owner = negative_reports["rows"][owner_index]
    verdicts = [
        json.loads(line)
        for line in (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    claim = next(row for row in verdicts if row["claim_id"] == "claim:gap-head-transfer-atlas")

    assert payload["gap_head_transfer_atlas"]["decision"] == "pass"
    assert payload["gap_head_transfer_atlas"]["discovery_level"] == atlas_row["discovery_level"]
    assert atlas_owner["terminal_verdict"] == "rejected"
    assert claim["claim_verdict"] == "ledger_only_hardening_not_ready"


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


def test_claim_verdict_writer_observes_current_scorecard_after_upstream_inputs(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    calls = []

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    def fake_formal_hardening(*, root, generated_at=None):
        calls.append("formal-hardening")
        path = root / canonical.FORMAL_HARDENING_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"ready": True, "recorded": 1, "required": 1, "gap_count": 0}, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (root / canonical.FORMAL_HARDENING_MARKDOWN_ARTIFACT).write_text("# formal\n", encoding="utf-8")
        return {"ready": True, "recorded": 1, "required": 1, "gap_count": 0}

    def fake_compile_discovery(*, root, generated_at=None, adapter=None):
        calls.append("discovery")
        path = root / canonical.DISCOVERY_MAP_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "generated_at": generated_at,
                    "row_count": 1,
                    "level_counts": {"D0": 1},
                    "rows": [
                        {
                            "report": "gap-head-discovery",
                            "json_artifact": "reports/canonical/gap-head-discovery.json",
                            "markdown_artifact": "reports/canonical/gap-head-discovery.md",
                            "discovery_level": "D0",
                            "terminal_verdict": "",
                            "classifier_reasons": [],
                            "projection_status": "projected",
                            "evidence_pointer": "$.positive_discovery",
                            "audit_status": "valid",
                            "audit_reason": "",
                        }
                    ],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        (root / canonical.DISCOVERY_MAP_MARKDOWN_ARTIFACT).write_text("# discovery\n", encoding="utf-8")
        return {"discovery_map": {"row_count": 1}}

    def fake_transfer(*, root, generated_at=None, require_anti_triviality=False):
        calls.append("dimension-transfer")
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "dimension_mismatch_debt_transfer": {
                        "status": "pass",
                        "base_level": "D4",
                        "effective_level": "D4",
                        "discovery_level": "D4",
                        "terminal_verdict": "ledger_only_hardening_not_ready",
                        "scope": "fixture",
                    },
                    "control_protocol": {},
                    "not_claimed": [],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        (root / canonical.DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT).write_text("# transfer\n", encoding="utf-8")
        return {}

    def fake_sidecar(*, root, generated_at=None):
        calls.append("dimension-sidecar")
        return {}

    def fake_claim_capsule(generated_at):
        return {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "D4",
            "terminal_verdict": "ledger_only_hardening_not_ready",
        }

    def fake_robustness(*, root, generated_at=None):
        calls.append("dimension-robustness")
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"status": "pass", "audit_status": "pass"}) + "\n", encoding="utf-8")
        (root / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT).write_text("# robust\n", encoding="utf-8")
        return {}

    def fake_witness_summary(*, root, generated_at=None):
        calls.append("witness-summary")
        path = root / canonical.NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"status": "pointer-only", "row_count": 0, "audit_status": "pass", "rows": []}) + "\n",
            encoding="utf-8",
        )
        (root / canonical.NEGATIVE_WITNESS_SUMMARY_MARKDOWN_ARTIFACT).write_text("# witness\n", encoding="utf-8")
        return {"status": "pointer-only", "row_count": 0, "audit_status": "pass"}

    def fake_build_witness_summary(*, root, generated_at=None):
        return {"status": "pointer-only", "row_count": 0, "audit_status": "pass"}

    def fake_mechanism(*, root, generated_at=None):
        return {}

    def fake_release(*, root, generated_at=None):
        return {}

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    monkeypatch.setattr(canonical, "_build_claim_capsule", fake_claim_capsule)
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_formal_hardening_report",
        types.SimpleNamespace(write_formal_hardening_report=fake_formal_hardening),
    )
    monkeypatch.setitem(
        sys.modules,
        "bedc_quality_lab.discovery_compiler.compiler",
        types.SimpleNamespace(compile_discovery=fake_compile_discovery),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_debt_transfer",
        types.SimpleNamespace(write_dimension_mismatch_debt_transfer=fake_transfer),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_anti_triviality",
        types.SimpleNamespace(write_dimension_mismatch_anti_triviality=fake_sidecar),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_transfer_robustness",
        types.SimpleNamespace(write_dimension_mismatch_transfer_robustness=fake_robustness),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_discovery_negative_witness_summary",
        types.SimpleNamespace(
            write_discovery_negative_witness_summary=fake_witness_summary,
            build_discovery_negative_witness_summary=fake_build_witness_summary,
        ),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_gap_head_mechanism_namecert",
        types.SimpleNamespace(write_gap_head_mechanism_namecert=fake_mechanism),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.release_manifest_sidecar",
        types.SimpleNamespace(write_release_manifest_sidecar=fake_release),
    )

    payload = canonical.run_reports(only="gap-head-discovery", generated_at="2030-01-01T00:00:00+00:00")
    rows = [
        json.loads(line)
        for line in (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    scorecard_hash = claim_verdict_demo.load_scorecard_snapshot(tmp_path).scorecard_hash

    assert calls.index("formal-hardening") < calls.index("discovery") < calls.index("witness-summary")
    assert rows
    assert all(row["scorecard_hash"] == scorecard_hash for row in rows)
    assert all(row["formal_hardening_ready"] is True for row in rows)
    assert payload["claim_verdicts"]["row_count"] == len(rows)


def test_committed_canonical_bundle_matches_registered_reports():
    from scripts import run_claim_verdict_demo as claim_verdicts
    from scripts import run_discovery_map as discovery_map

    canonical_dir = canonical.ROOT / "reports" / "canonical"
    discovery_payload = json.loads((canonical_dir / "discovery_map.json").read_text(encoding="utf-8"))
    claim_rows = [
        json.loads(line)
        for line in (canonical_dir / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    index_payload = json.loads((canonical_dir / "index.json").read_text(encoding="utf-8"))
    spec_names = {spec.name for spec in canonical.CANONICAL_REPORTS}

    assert {row["report"] for row in discovery_payload["rows"]}.issuperset(spec_names)
    assert {row["claim_id"].removeprefix("claim:") for row in claim_rows if row["claim_id"].startswith("claim:")}.issuperset(spec_names)
    assert {row["name"] for row in index_payload["reports"]} == spec_names

    regenerated_discovery = discovery_map.build_discovery_map(
        generated_at=discovery_payload["generated_at"],
        root=canonical.ROOT,
        canonical_reports=canonical.CANONICAL_REPORTS,
    )
    regenerated_claim_rows = claim_verdicts.compile_claim_verdicts(
        canonical.ROOT,
        generated_at=discovery_payload["generated_at"],
    )
    regenerated_index = canonical._index(
        index_payload["reports"],
        generated_at=index_payload["generated_at"],
        claim_verdict_rows=regenerated_claim_rows,
    )

    assert discovery_payload == regenerated_discovery
    assert claim_rows == regenerated_claim_rows
    assert index_payload == regenerated_index


def test_claim_capsule_is_generated_and_not_canonical_report_artifact(tmp_path, monkeypatch):
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

    def write_transfer(*, root, generated_at=None, require_anti_triviality=True):
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "dimension_mismatch_debt_transfer": {
                "status": "pass",
                "base_level": "D4",
                "anti_triviality_status": "scale_leakage_detected" if require_anti_triviality else None,
                "effective_level": "DN" if require_anti_triviality else "D4",
                "downgrade_reason": "scale_only_or_metadata_proxy_sufficient" if require_anti_triviality else None,
                "terminal_verdict": "negative_discovery" if require_anti_triviality else "source_pass",
                "hypothesis": "fixture hypothesis",
                "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status" if require_anti_triviality else None,
                "what_was_learned": "fixture learned",
            }
        }
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return payload

    def write_sidecar(*, root, generated_at=None):
        path = root / "reports/dimension_mismatch_anti_triviality.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {"status": "scale_leakage_detected", "recommended_projection": "demote_to_DN_or_D1"}
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return payload

    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_debt_transfer",
        types.SimpleNamespace(write_dimension_mismatch_debt_transfer=write_transfer),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_anti_triviality",
        types.SimpleNamespace(write_dimension_mismatch_anti_triviality=write_sidecar),
    )

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    capsule_path = canonical.CANONICAL_DIR / "claim_capsule.json"
    capsule = json.loads(capsule_path.read_text(encoding="utf-8"))
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert payload["claim_capsule"]["json_artifact"] == "reports/canonical/claim_capsule.json"
    assert payload["claim_capsule"]["capsule_status"] == "complete"
    assert "reports/canonical/claim_capsule.json" not in json_artifacts
    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["status"] == "complete"
    assert capsule["effective_level"] == "DN"
    assert capsule["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"
    assert {
        "global dimension theory",
        "representation-geometric debt transfer",
        "D5 promotion",
        "global model quality",
        "full LeJEPA",
        "full TensorNameCert",
        "LLM behavior",
        "mechanism closure unless D5-M",
    }.issubset(set(capsule["not_claimed"]))


def test_claim_capsule_missing_source_node_is_incomplete_not_synthetic_dn(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    capsule = canonical._build_claim_capsule("fixture-time")

    assert capsule["status"] == "incomplete"
    assert capsule["reason"] == "source claim node is missing"
    assert "effective_level" not in capsule
    assert "terminal_verdict" not in capsule


def test_claim_capsule_missing_required_cells_is_incomplete_not_synthetic_dn(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"dimension_mismatch_debt_transfer": {"base_level": "D4"}}) + "\n", encoding="utf-8")

    capsule = canonical._build_claim_capsule("fixture-time")

    assert capsule["status"] == "incomplete"
    assert "effective_level" in capsule["missing_cells"]
    assert "terminal_verdict" in capsule["missing_cells"]


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
                    "report": "gap-head-transfer-atlas",
                    "artifact": "reports/canonical/gap_head_transfer_atlas.json",
                    "pointer": "$.not_claimed",
                },
                {
                    "report": "gap-head-attribution-capsule",
                    "artifact": "reports/canonical/gap_head_attribution_capsule.json",
                    "pointer": "$.scope.not_claimed",
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
                    "report": "sigreg-training-proxy",
                    "artifact": "reports/canonical/sigreg-training-proxy.json",
                    "pointer": "$.arm_protocol",
                },
                {
                    "report": "spectral-ablation-hinge",
                    "artifact": "reports/canonical/spectral-ablation-hinge.json",
                    "pointer": "$.applicability_boundary",
                },
            ],
            "numerator": 13,
            "denominator": 13,
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
                    "report": "gap-head-transfer-atlas",
                    "artifact": "reports/canonical/gap_head_transfer_atlas.json",
                    "pointer": "$.source_artifacts.metric_helper",
                },
                {
                    "report": "gap-head-attribution-capsule",
                    "artifact": "reports/canonical/gap_head_attribution_capsule.json",
                    "pointer": "$.cost_protocol_pointer",
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
                    "report": "sigreg-training-proxy",
                    "artifact": "reports/canonical/sigreg-training-proxy.json",
                    "pointer": "$.source_artifacts.cost_protocol",
                },
                {
                    "report": "spectral-ablation-hinge",
                    "artifact": "reports/canonical/spectral-ablation-hinge.json",
                    "pointer": "$.source_artifacts",
                },
            ],
            "numerator": 13,
            "denominator": 13,
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


def test_positive_discovery_count_is_limited_to_discovery_producers(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["PositiveDiscoveryCount"]
    assert row["status"] == "ready"
    assert row["denominator"] == 2
    assert row["source"] == [
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
    ]


def test_attribution_capsule_d5_cells_project_minimal_two_axis_discovery_map_row(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
        _mutate_payload(
            canonical,
            "gap-head-attribution-capsule",
            lambda payload: payload.update(
                {
                    "d5_o": {"status": "ready"},
                    "d5_m": {"status": "blocked", "passed": False, "failed_gate": "A1-HG3"},
                    "mechanism_case": {"status": "D5-O retained, mechanism = probe-margin-channel"},
                }
            ),
        )

        payload = discovery_map.build_discovery_map(
            generated_at="fixture-time",
            root=tmp_path,
            canonical_reports=canonical.CANONICAL_REPORTS,
        )
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
    row = {item["report"]: item for item in payload["rows"]}[spec.name]

    assert row["discovery_level"] == "D0"
    assert row["projection_status"] == "two-axis-recorded"
    assert row["evidence_pointer"] == spec.positive_claim_pointer
    assert row["base_level"] == "D5-O"
    assert row["base_status"] == "ready"
    assert row["mechanism_level"] == "blocked"
    assert row["mechanism_status"] == "blocked"
    assert row["mechanism_channel"] == "probe-margin-channel"
    assert row["mechanism_failed_gate"] == "A1-HG3"
    assert row["operational_pointer"] == "$.d5_o"
    assert row["mechanism_pointer"] == "$.d5_m"
    assert row["mechanism_case_pointer"] == "$.mechanism_case"
    assert row["mechanism_namecert_pointer"] == "reports/gap_head_mechanism_namecert.json"
    assert row["mechanism_ledger_pointer"] == "reports/gap_head_mechanism_namecert.json:$.ledger_policy.mechanism_closure_debt"
    assert row["mechanism_closure_pointer"] == "reports/gap_head_mechanism_namecert.json:$.closure_status.mechanism_spec"
    assert row["audit_status"] == "valid"


def test_attribution_capsule_sidecar_and_discovery_map_levels_are_consistent():
    capsule = json.loads((canonical.ROOT / "reports/canonical/gap_head_attribution_capsule.json").read_text(encoding="utf-8"))
    sidecar = json.loads((canonical.ROOT / "reports/gap_head_mechanism_namecert.json").read_text(encoding="utf-8"))
    discovery = json.loads((canonical.ROOT / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()

    row = {item["report"]: item for item in discovery["rows"]}["gap-head-attribution-capsule"]
    index_row = {item["name"]: item for item in index["reports"]}["gap-head-attribution-capsule"]
    claim_row = {item["claim_id"]: item for item in claim_rows}["claim:gap-head-attribution-capsule"]
    row_index = next(
        index
        for index, item in enumerate(discovery["rows"])
        if item["report"] == "gap-head-attribution-capsule"
    )

    assert index_row["json_artifact"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert row["json_artifact"] == index_row["json_artifact"]
    assert claim_row["ledger_pointer"] == f"reports/canonical/discovery_map.json:$.rows[{row_index}].discovery_level"
    assert claim_row["source"] == "reports/canonical/gap_head_attribution_capsule.json:$.d5_m"
    assert capsule["d5_o"]["status"] == row["base_status"] == "ready"
    assert row["base_level"] == "D5-O"
    assert sidecar["ledger_policy"]["mechanism_closure_debt"] == "open"
    assert sidecar["closure_status"]["mechanism_spec"] == "partial"
    assert row["mechanism_status"] == "blocked"
    assert row["mechanism_level"] == "blocked"
    assert capsule["d5_m"]["failed_gate"] == sidecar["mechanism_spec"]["a1_failed_gate"] == row["mechanism_failed_gate"]
    assert capsule["mechanism_case"]["status"] == sidecar["mechanism_spec"]["a1_mechanism_status"]
    assert sidecar["mechanism_spec"]["candidate_mechanism"] == capsule["mechanism_case"]["candidate_mechanism"]
    assert row["mechanism_channel"] == sidecar["mechanism_spec"]["candidate_mechanism"]
    assert row["mechanism_ledger_pointer"] == "reports/gap_head_mechanism_namecert.json:$.ledger_policy.mechanism_closure_debt"
    assert row["mechanism_closure_pointer"] == "reports/gap_head_mechanism_namecert.json:$.closure_status.mechanism_spec"


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


def test_quality_scorecard_cost_protocol_completeness_fails_closed_for_dangling_indirect_pointer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        _mutate_payload(
            canonical,
            "gap-head-attribution-capsule",
            lambda payload: payload.update({"cost_protocol_pointer": "$.source_artifacts.missing_cost_protocol"}),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["CostProtocolCompleteness"]
    assert row["status"] == "not-ready"
    assert row["dependency"] == "gap-head-attribution-capsule:$.cost_protocol_pointer"
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


def test_release_manifest_sidecar_index_summary_is_pointer_only(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    (tmp_path / "reports").mkdir(parents=True)
    (tmp_path / "reports" / "release_manifest_sidecar.json").write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:release-manifest-sidecar",
                "artifact_id": "bedc-quality-lab:release-manifest-sidecar",
                "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
                "release_bundle_status": "ready",
                "tag_status": "absent",
                "version": "0.0.1",
                "required_pointers": [{"id": "canonical-index"}],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    section = canonical._release_manifest_sidecar_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:release-manifest-sidecar",
        "json_artifact": "reports/release_manifest_sidecar.json",
        "markdown_artifact": "reports/release_manifest_sidecar.md",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "release_bundle_status": "ready",
        "tag_status": "absent",
        "version": "0.0.1",
    }
    assert payload["release_manifest_sidecar"] == section
    assert set(section) == {
        "status",
        "artifact_id",
        "json_artifact",
        "markdown_artifact",
        "canonical_role",
        "release_bundle_status",
        "tag_status",
        "version",
    }
    assert "release_manifest_sidecar" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "required_pointers" not in json.dumps(payload["release_manifest_sidecar"])
    assert "release_manifest_sidecar" not in json.dumps(payload["discovery_map"])
    assert "Release manifest sidecar" in markdown

import json
from pathlib import Path

import numpy as np
import pytest

from bedc_quality_lab.backends.current_lab.gap_head_readiness import (
    GAP_HEAD_ABLATION_ARTIFACT,
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
    GapHeadOperationalReadinessPolicy,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from scripts.experiment_stats import metric_stats
from scripts import run_gap_head_attribution_capsule as runner
from scripts import run_canonical_reports as canonical


EXPECTED_ARMS = (
    "full",
    "h_only",
    "h_centered_only",
    "h_normalized_no_scale",
    "h_direction_only",
    "h_norm_only",
    "h_random_rotation",
    "h_random_projection_lowdim",
    "score_only",
    "margin_only",
    "score_plus_margin",
    "transition_delta_only",
    "quality_scalars_only",
    "h_plus_margin",
    "h_plus_transition",
    "h_plus_quality",
    "full_without_h",
    "full_without_score",
    "full_without_margin",
    "full_without_transition",
    "full_without_quality_scalars",
    "full_residualized_against_score_margin",
    "full_without_score_and_margin",
    "matched_random",
)
A1_CANONICAL_HG3 = {
    "criterion": "full AUROC CI-low > score_plus_margin AUROC CI-high",
    "evidence": {
        "full_ci_low": 0.7996948122113381,
        "score_plus_margin_ci_high": 0.8454823105481024,
    },
    "name": "A1-HG3",
    "status": "fail",
}
A1_CANONICAL_NEGATIVE_WITNESS_ROW = {
    "witness_id": "a1-hg3-score-plus-margin-competitive",
    "source_artifact": "reports/runs/a1-canonical/claim_capsule.json",
    "source_pointer": "$.hardgates.gates.A1-HG3",
    "bedc_gap_field": "d5_m.failed_gate",
    "demotion_rule": "block D5-M while A1-HG3 fails",
    "regression_test": (
        "tests/test_gap_head_attribution_capsule.py::"
        "test_a1_run_local_negative_witness_records_a1_hg3_failure"
    ),
    "evidence_pointer": "$.hardgates.gates.A1-HG3",
    "status": "fail",
    "reason": (
        "A1-HG3 failed because full AUROC CI-low does not exceed the score_plus_margin AUROC "
        "CI-high control; D5-M remains blocked."
    ),
}


def _stat(value):
    return metric_stats([float(value)] * 4)


def _auroc_cell(*, mean, ci95_low, ci95_high):
    return {
        "ci95_half_width": 0.01,
        "ci95_high": ci95_high,
        "ci95_low": ci95_low,
        "mean": mean,
        "n": 10,
        "std": 0.01,
    }


def _readiness_context(*, ablation_status="pass"):
    return {
        GAP_HEAD_ROBUSTNESS_ARTIFACT: {
            "final_status": "pass",
            "A1_threshold_sweep": {"treatment_verdict": {"positive": True}},
            "A3_seed_expansion": {"final_verdict": "robust_positive"},
        },
        GAP_HEAD_ABLATION_ARTIFACT: {"hardgate": {"status": ablation_status}},
        NEGATIVE_WITNESSES_ARTIFACT: {
            "status": "pointer-only",
            "expected_kind_count": 9,
            "witnesses": [
                {"kind": f"witness-{index}", "terminal_verdict": "rejected", "discovery_level": "DN"}
                for index in range(9)
            ],
        },
        OBSERVED_DEBT_ARTIFACT: {
            "gap_head_on_h_observed_debt_transfer": {"status": "pass"},
            "surfaces": [
                {
                    "control_verdict": {"positive": False},
                    "hardgates": {
                        "HG-A1": {
                            "learned_auroc": _auroc_cell(mean=0.82, ci95_low=0.81, ci95_high=0.83),
                            "matched_random_auroc": _auroc_cell(mean=0.46, ci95_low=0.42, ci95_high=0.49),
                        }
                    },
                }
            ],
            "not_claimed": ["no claim outside the listed observed-debt transfer surfaces"],
        },
    }


def _readiness_ledger(*, ablation_status="pass"):
    return GapHeadOperationalReadinessPolicy().criteria(_readiness_context(ablation_status=ablation_status))


def _write_readiness_context(root: Path, *, ablation_status="pass"):
    for artifact, payload in _readiness_context(ablation_status=ablation_status).items():
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _row(auroc, reduction):
    return {
        "record_count": 4,
        "family": "fixture",
        "feature_roots": ["fixture"],
        "feature_column_count": 1,
        "control_role": "fixture",
        "gate_role": "fixture",
        "seed_policy": "none",
        "AUROC": _stat(auroc),
        "UnloggedErrorRate": _stat(0.5 - reduction),
        "UER_reduction": _stat(reduction),
        "CriticalUnloggedErrorRate": _stat(0.1),
        "FalseLedgerRate": _stat(0.2),
        "NetInformation": _stat(0.8),
        "PositiveDiscovery": True,
    }


def _aggregate(**overrides):
    values = {
        "full": (0.86, 0.40),
        "h_only": (0.78, 0.28),
        "h_centered_only": (0.78, 0.28),
        "h_normalized_no_scale": (0.78, 0.28),
        "h_direction_only": (0.77, 0.27),
        "h_norm_only": (0.55, 0.02),
        "h_random_rotation": (0.76, 0.26),
        "h_random_projection_lowdim": (0.65, 0.15),
        "score_only": (0.58, 0.05),
        "margin_only": (0.56, 0.04),
        "score_plus_margin": (0.57, 0.05),
        "transition_delta_only": (0.55, 0.03),
        "quality_scalars_only": (0.52, 0.01),
        "h_plus_margin": (0.74, 0.24),
        "h_plus_transition": (0.75, 0.25),
        "h_plus_quality": (0.74, 0.24),
        "full_without_h": (0.64, 0.16),
        "full_without_score": (0.82, 0.36),
        "full_without_margin": (0.80, 0.34),
        "full_without_transition": (0.78, 0.31),
        "full_without_quality_scalars": (0.84, 0.38),
        "full_residualized_against_score_margin": (0.84, 0.36),
        "full_without_score_and_margin": (0.82, 0.34),
        "matched_random": (0.51, 0.01),
    }
    values.update(overrides)
    return {
        "record_count": 4 * len(EXPECTED_ARMS),
        "seed_order": [1, 2, 3, 4],
        "arm_order": list(EXPECTED_ARMS),
        "by_arm": {arm: _row(*values[arm]) for arm in EXPECTED_ARMS},
    }


def _resolve_pointer(payload, pointer):
    value = pointer_value(payload, pointer)
    if value is None:
        raise KeyError(pointer)
    return value


def _pointer_resolves(payload, pointer):
    return pointer_value(payload, pointer) is not None


def _contains_key(payload, forbidden):
    if isinstance(payload, dict):
        return forbidden in payload or any(_contains_key(value, forbidden) for value in payload.values())
    if isinstance(payload, list):
        return any(_contains_key(value, forbidden) for value in payload)
    return False


def _node_at_path(payload, path):
    if path == "$":
        return payload
    value = pointer_value(payload, path)
    if value is None:
        raise KeyError(path)
    return value


def _lab_root_for_artifact(artifact):
    for parent in artifact.parents:
        if parent.name == "reports":
            return parent.parent
    return artifact.parent.parent.parent


def _collect_pointers(obj, path="$", *, collect_all_strings=False):
    found = []
    if isinstance(obj, dict):
        for key, value in obj.items():
            key_path = f"{path}.{key}"
            found.extend(
                _collect_pointers(
                    value,
                    key_path,
                    collect_all_strings=collect_all_strings or key.endswith("_pointer"),
                )
            )
    elif isinstance(obj, list):
        for index, value in enumerate(obj):
            found.extend(_collect_pointers(value, f"{path}.{index}", collect_all_strings=collect_all_strings))
    elif isinstance(obj, str) and obj.startswith("$."):
        found.append((path, obj))
    return found


def _pointer_target_payload(artifact, doc, pointer_path):
    root = _lab_root_for_artifact(artifact)
    if pointer_path == "$.source_pointer":
        source_artifact = doc.get("source")
        if isinstance(source_artifact, str) and (root / source_artifact).exists():
            return json.loads((root / source_artifact).read_text(encoding="utf-8"))
    parent_path = pointer_path.rsplit(".", 1)[0]
    parent = _node_at_path(doc, parent_path)
    if isinstance(parent, dict):
        target_artifact = parent.get("json_artifact") or parent.get("artifact")
        if target_artifact:
            return json.loads((root / target_artifact).read_text(encoding="utf-8"))
    if pointer_path == "$.summary_pointer":
        summary_artifact = doc.get("source_artifacts", {}).get("summary")
        if summary_artifact:
            return json.loads((root / summary_artifact).read_text(encoding="utf-8"))
    if artifact.name == "discovery_map.json" and pointer_path.startswith("$.rows."):
        row = doc["rows"][int(pointer_path.split(".")[2])]
        parts = pointer_path.split(".")
        if len(parts) >= 6 and parts[3] == "d5_readiness" and parts[5] == "pointer":
            readiness = row["d5_readiness"][parts[4]]
            return json.loads((root / readiness["artifact"]).read_text(encoding="utf-8"))
        return json.loads((root / row["json_artifact"]).read_text(encoding="utf-8"))
    if pointer_path.startswith("$.d5_o.readiness.") and pointer_path.endswith(".pointer"):
        parts = pointer_path.split(".")
        readiness = doc["d5_o"]["readiness"][parts[3]]
        return json.loads((root / readiness["artifact"]).read_text(encoding="utf-8"))
    if artifact.name == "index.json" and pointer_path.startswith("$.reports."):
        report = doc["reports"][int(pointer_path.split(".")[2])]
        return json.loads((root / report["json_artifact"]).read_text(encoding="utf-8"))
    if artifact.name == "index.json" and pointer_path.startswith("$.claims_nonclaims.positive_claim_cells."):
        cell = doc["claims_nonclaims"]["positive_claim_cells"][int(pointer_path.split(".")[3])]
        spec = canonical._specs_by_name()[cell["report"]]
        return json.loads((root / spec.json_artifact).read_text(encoding="utf-8"))
    return doc


def _artifact_payload(pointer="$.source_artifacts.cost_protocol"):
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    head_patch = runner._finalize_head_channel_patch_evidence({"head_channel_patch_evidence": _head_patch_fixture()})
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, head_patch)
    residualized_claim = runner._residualized_attribution_claim(aggregate, residualized, score_margin, a4_hardgates)
    e_hardgates = runner._e_hardgates(aggregate, residualized_claim)
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)
    d5_m = runner._d5_m(hardgates, a4_hardgates)
    source_artifacts = {
        "artifact_id": runner.ARTIFACT_ID,
        "source_issue": 692,
        "generation_script": "scripts/run_gap_head_attribution_capsule.py",
        "cost_protocol": {"status": "recorded", "unit": "fixture"},
    }
    d5_o = runner._d5_o(aggregate, _readiness_ledger())
    mechanism_evidence = runner._mechanism_evidence(d5_o, d5_m, case, a4_hardgates, residualized, score_margin, head_patch)
    return {
        "schema_id": runner.SCHEMA_ID,
        "source_issue": 692,
        "source_issues": [692, 747, 750],
        "artifact_id": runner.ARTIFACT_ID,
        "run_id": "a1-fixture",
        "generated_at": "2026-01-02T03:04:05+00:00",
        "d5_o": d5_o,
        "d5_m": d5_m,
        "mechanism_case": case,
        "mechanism_evidence": mechanism_evidence,
        "not_implemented": list(runner.NOT_IMPLEMENTED),
        "ledger_debt": runner._ledger_debt(mechanism_evidence),
        "hardgates": hardgates,
        "residualized_attribution": residualized,
        "residualized_attribution_claim": residualized_claim,
        "e_hardgates": e_hardgates,
        "score_margin_causal_evidence": score_margin,
        "head_channel_patch_evidence": head_patch,
        "a4_hardgates": a4_hardgates,
        "claim_capsule_hardgates": {"CC-HG6": {"name": "CC-HG6", "status": "unchecked"}},
        "cost_protocol_pointer": pointer,
        "control_pointer": runner._control_pointer(),
        "control_evidence": runner._control_evidence(aggregate),
        "scope_seal": runner._scope_seal(),
        "forbidden_column_audit": runner._forbidden_column_audit({arm: ["h:0"] for arm in runner.ARM_NAMES}),
        "failed_gate": None,
        "what_was_learned": case["what_was_learned"],
        "revocation_ledger": runner._revocation_ledger(hardgates, "2026-01-02T03:04:05+00:00", d5_m),
        "positive_discovery_inputs": ["A1-HG1", "A1-HG2"],
        "config": {"sample_count": 8, "seed_count": 1},
        "source_artifacts": source_artifacts,
        "aggregate": aggregate,
        "records": [{"arm": arm, "fixture": True} for arm in runner.ARM_NAMES],
        "scope": {"not_claimed": list(runner.NOT_CLAIMED)},
    }


def _a1_canonical_negative_witness_payload():
    payload = _artifact_payload()
    payload["run_id"] = "a1-canonical"
    payload["failed_gate"] = "A1-HG3"
    payload["d5_m"] = {**payload["d5_m"], "status": "blocked", "passed": False, "failed_gate": "A1-HG3"}
    payload["hardgates"] = {
        **payload["hardgates"],
        "status": "fail",
        "failed_gate": "A1-HG3",
        "gates": {
            **payload["hardgates"]["gates"],
            "A1-HG3": dict(A1_CANONICAL_HG3),
        },
    }
    return payload


def _write_a1_canonical_negative_witness_artifacts(tmp_path, *, canonical=False):
    payload = _a1_canonical_negative_witness_payload()
    run_dir = tmp_path / "reports/runs/a1-canonical"
    old_root = runner.ROOT
    try:
        if canonical:
            runner.ROOT = tmp_path
            test_file = tmp_path / "tests/test_gap_head_attribution_capsule.py"
            test_file.parent.mkdir(parents=True, exist_ok=True)
            test_file.write_text(
                "def test_a1_run_local_negative_witness_records_a1_hg3_failure():\n"
                "    pass\n",
                encoding="utf-8",
            )
        runner._write_artifacts(payload, run_dir, canonical=canonical)
    finally:
        runner.ROOT = old_root
    return {
        "claim_capsule": json.loads((run_dir / "claim_capsule.json").read_text(encoding="utf-8")),
        "summary": json.loads((run_dir / "summary.json").read_text(encoding="utf-8")),
        "report": (run_dir / "report.md").read_text(encoding="utf-8"),
        "canonical": (
            json.loads((tmp_path / runner.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
            if canonical
            else None
        ),
    }


def _residualized_fixture(aggregate, *, status="pass"):
    return {
        "status": status,
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution",
        "guard_outcomes": {
            "finite_values": status,
            "rank_guard": status,
            "condition_number_guard": status,
            "deterministic_construction": status,
            "score_margin_correlation_removal": status,
        },
        "residualization_metadata": [{"seed": seed, "residualization": {"finite_values": status == "pass"}} for seed in aggregate["seed_order"]],
        "a4_arm_order": ["full_residualized_against_score_margin", "full_without_score_and_margin"],
        "per_seed_arm_metrics": [],
        "ci_summaries": {
            arm: {
                "AUROC": aggregate["by_arm"][arm]["AUROC"],
                "UER_reduction": aggregate["by_arm"][arm]["UER_reduction"],
            }
            for arm in ("full_residualized_against_score_margin", "full_without_score_and_margin")
        },
    }


def _score_margin_fixture(classification="not_score_margin_sufficient", *, status="pass"):
    ci_summaries = {
        "shuffle_score_margin": {
            "AUROC_after_minus_before": {"mean": -0.05},
            "UER_after_minus_before": {"mean": 0.01},
        },
        "replace_high_gap_score_margin_from_low_gap": {
            "AUROC_after_minus_before": {"mean": -0.06},
            "UER_after_minus_before": {"mean": 0.01},
        },
    }
    return {
        "status": status,
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "deterministic_salts": {
            "shuffle_score_margin": runner.SCORE_MARGIN_SHUFFLE_SALT,
            "replace_high_gap_score_margin_from_low_gap": runner.SCORE_MARGIN_REPLACE_SALT,
        },
        "shuffle_score_margin": {"per_seed_before_after_metrics": [], "ci_summaries": ci_summaries["shuffle_score_margin"]},
        "replace_high_gap_score_margin_from_low_gap": {"per_seed_before_after_metrics": [], "ci_summaries": ci_summaries["replace_high_gap_score_margin_from_low_gap"]},
        "paired_deltas": [{"seed": 1, "same_seed": True, "same_arm_fit_path": True, "same_metric_set": True}],
        "channel_classification": classification,
        "protocol_checks": {
            "present": True,
            "deterministic": True,
            "finite": True,
            "seed_paired": True,
            "column_audited": True,
            "classified": True,
        },
        "ci_summaries": ci_summaries,
    }


def _head_patch_fixture(*, status="pass", gate_status="pass", auroc_delta=-0.08, uer_delta=0.04):
    ci_summaries = {
        "null_head": {
            "AUROC_after_minus_before": {"mean": auroc_delta, "ci95_low": auroc_delta, "ci95_high": auroc_delta},
            "UER_after_minus_before": {"mean": uer_delta, "ci95_low": uer_delta, "ci95_high": uer_delta},
            "UER_reduction_after_minus_before": {"mean": -uer_delta, "ci95_low": -uer_delta, "ci95_high": -uer_delta},
        },
        "permute_head_rows": {
            "AUROC_after_minus_before": {"mean": auroc_delta - 0.01, "ci95_low": auroc_delta - 0.01, "ci95_high": auroc_delta - 0.01},
            "UER_after_minus_before": {"mean": uer_delta, "ci95_low": uer_delta, "ci95_high": uer_delta},
            "UER_reduction_after_minus_before": {"mean": -uer_delta, "ci95_low": -uer_delta, "ci95_high": -uer_delta},
        },
    }
    audit = {
        "touched_column_audit": {
            "status": "pass",
            "allowed_roots": ["h"],
            "touched_roots": ["h"],
            "touched_columns": ["h:0", "h:1"],
            "unchanged_non_h_columns": True,
            "train_features_unchanged": True,
            "eval_features_changed": True,
        }
    }
    evidence = {
        "status": status,
        "gate_status": gate_status,
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.head_channel_patch_evidence",
        "deterministic_salts": {
            "null_head": None,
            "permute_head_rows": runner.HEAD_PATCH_PERMUTE_SALT,
        },
        "null_head": {"per_seed_before_after_metrics": [{"seed": 1, "audit": audit}], "ci_summaries": ci_summaries["null_head"]},
        "permute_head_rows": {"per_seed_before_after_metrics": [{"seed": 1, "audit": audit}], "ci_summaries": ci_summaries["permute_head_rows"]},
        "paired_deltas": [{"seed": 1, "same_seed": True, "same_full_arm_fit_path": True, "same_metric_set": True}],
        "protocol_checks": {
            "present": True,
            "deterministic": True,
            "finite": True,
            "seed_paired": True,
            "column_audited": True,
            "eval_only_patch": True,
            "required_modes_present": True,
        },
        "gate_criterion": "both head patches have AUROC delta CI-high < -0.02 and UER delta CI-low >= 0.0",
        "gate_evidence": {
            "auroc_drop": gate_status == "pass",
            "uer_not_improved": True,
        },
        "ci_summaries": ci_summaries,
    }
    evidence["causal_patch_claim"] = runner._head_patch_causal_claim(evidence)
    return evidence


def _residualized_claim_fixture(aggregate, *, residualized=None, score_margin=None, a4_hardgates=None):
    residualized = _residualized_fixture(aggregate) if residualized is None else residualized
    score_margin = _score_margin_fixture("not_score_margin_sufficient") if score_margin is None else score_margin
    if a4_hardgates is None:
        head_patch = runner._finalize_head_channel_patch_evidence({"head_channel_patch_evidence": _head_patch_fixture()})
        a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, head_patch)
    return runner._residualized_attribution_claim(aggregate, residualized, score_margin, a4_hardgates)


def _artifact_pointer_resolves(payload, artifact_pointer):
    artifact, pointer = artifact_pointer.split(":", 1)
    assert artifact == runner.CANONICAL_JSON_ARTIFACT
    return pointer_value(payload, pointer) is not None


def test_arm_registry_order_and_private_spec_shape():
    assert runner.ARM_NAMES == EXPECTED_ARMS
    assert [spec.name for spec in runner.attribution_arm_specs()] == list(EXPECTED_ARMS)
    assert runner.ARM_SPECS[0].gate_role == "primary"
    assert runner.ARM_SPECS[-1].control_role == "matched_random_gap_labels"


def test_feature_constructions_match_maintainer_spec():
    h = np.array([[1.0, 2.0], [3.0, 6.0], [5.0, 10.0]], dtype=np.float64)
    h_pair = np.array([[2.0, 2.0], [4.0, 9.0], [8.0, 14.0]], dtype=np.float64)
    centered = h - h.mean(axis=0, keepdims=True)

    np.testing.assert_allclose(runner.h_centered_only(h), centered)
    np.testing.assert_allclose(
        runner.h_normalized_no_scale(h),
        centered / (np.linalg.norm(centered, axis=1, keepdims=True) + 1e-8),
    )
    np.testing.assert_allclose(
        runner.h_norm_only(h, h_pair),
        np.stack(
            [
                np.linalg.norm(h, axis=1),
                np.linalg.norm(h_pair - h, axis=1),
                np.std(h, axis=1),
                np.max(np.abs(h), axis=1),
            ],
            axis=1,
        ),
    )
    score = np.array([0.2, 0.7, 0.4])
    threshold = np.array([0.5, 0.5, 0.5])
    np.testing.assert_allclose(
        runner.score_plus_margin(score, threshold),
        np.stack([score, np.abs(score - threshold), score >= threshold], axis=1),
    )


def test_feature_builders_reject_forbidden_columns_and_controls_use_h_only():
    assert runner._forbidden_column_audit({"full": ["h:0", "score:a"]})["status"] == "pass"
    assert runner._forbidden_column_audit({"bad": ["z"]})["status"] == "fail"
    assert runner.FORBIDDEN_INFERENCE_COLUMNS is runner.source.FORBIDDEN_INFERENCE_COLUMNS
    assert not hasattr(runner, "FORBIDDEN_COLUMNS")
    text = json.dumps(
        {
            spec.name: {
                "roots": spec.feature_roots,
                "control": spec.control_role,
            }
            for spec in runner.ARM_SPECS
            if spec.name in {"h_random_rotation", "h_random_projection_lowdim"}
        }
    )
    assert "label" not in text
    assert "prediction_error" not in text
    assert "config_metadata" not in text


@pytest.mark.parametrize("column", ["z", "label", "config_metadata.seed"])
def test_forbidden_column_audit_delegates_to_source_vocabulary(column):
    audit = runner._forbidden_column_audit({"bad": ["h:0", column]})

    assert audit["status"] == "fail"
    assert audit["forbidden_columns"] == list(runner.source.FORBIDDEN_INFERENCE_COLUMNS)
    assert audit["forbidden_inference_columns"] == list(runner.source.FORBIDDEN_INFERENCE_COLUMNS)
    assert audit["violations"][0]["arm"] == "bad"
    assert audit["violations"][0]["columns"] == [column]
    assert audit["violations"][0]["failed_gate"] == "forbidden-inference-column"


def test_seeded_rotation_and_projection_are_deterministic():
    h = np.array([[1.0, 2.0], [3.0, 5.0], [7.0, 11.0]], dtype=np.float64)
    rot_a, seed_a = runner._orthogonal_rotation(h, seed=10)
    rot_b, seed_b = runner._orthogonal_rotation(h, seed=10)
    proj_a, proj_seed_a = runner._gaussian_projection(h, seed=10)
    proj_b, proj_seed_b = runner._gaussian_projection(h, seed=10)

    assert seed_a == seed_b
    assert proj_seed_a == proj_seed_b
    np.testing.assert_allclose(rot_a, rot_b)
    np.testing.assert_allclose(proj_a, proj_b)
    assert proj_a.shape == (3, 1)


def test_head_patch_eval_features_are_deterministic_and_audited():
    surface = {
        "feature_columns": ["h:0", "h:1", "score:a", "margin:a", "transition_delta:a", "quality:q"],
        "features": np.array(
            [
                [1.0, 3.0, 0.1, 0.9, 0.0, 1.0],
                [2.0, 5.0, 0.2, 0.7, 0.1, 1.0],
                [3.0, 7.0, 0.3, 0.8, 0.0, 1.0],
                [4.0, 9.0, 0.4, 0.4, 0.1, 1.0],
                [5.0, 11.0, 0.5, 0.6, 0.0, 1.0],
            ],
            dtype=np.float64,
        ),
        "train_idx": np.array([0, 1], dtype=np.int64),
        "eval_idx": np.array([2, 3, 4], dtype=np.int64),
    }

    null_features, null_audit = runner._head_patched_eval_features(surface, seed=17, mode="null_head")
    permuted_a, permutation_audit = runner._head_patched_eval_features(surface, seed=17, mode="permute_head_rows")
    permuted_b, repeat_audit = runner._head_patched_eval_features(surface, seed=17, mode="permute_head_rows")

    np.testing.assert_allclose(null_features[surface["eval_idx"], :2], 0.0)
    np.testing.assert_allclose(null_features[surface["train_idx"]], surface["features"][surface["train_idx"]])
    np.testing.assert_allclose(permuted_a, permuted_b)
    assert permutation_audit == repeat_audit
    for audit in (null_audit, permutation_audit):
        touched = audit["touched_column_audit"]
        assert touched["status"] == "pass"
        assert touched["touched_roots"] == ["h"]
        assert touched["touched_columns"] == ["h:0", "h:1"]
        assert touched["train_features_unchanged"] is True
        assert touched["eval_features_changed"] is True
        assert touched["unchanged_non_h_columns"] is True


def test_head_patch_touched_column_audit_fails_when_non_h_column_changes():
    surface = {
        "feature_columns": ["h:0", "score:a"],
        "features": np.array(
            [
                [1.0, 0.1],
                [2.0, 0.2],
                [3.0, 0.3],
                [4.0, 0.4],
            ],
            dtype=np.float64,
        ),
        "train_idx": np.array([0, 1], dtype=np.int64),
        "eval_idx": np.array([2, 3], dtype=np.int64),
    }
    changed, audit = runner._head_patched_eval_features(surface, seed=17, mode="null_head")
    changed[surface["eval_idx"], 1] = 0.0
    before = surface["features"]
    moved = np.abs(changed - before) > 1.0e-12
    touched_columns = [
        surface["feature_columns"][index]
        for index, value in enumerate(np.any(moved, axis=0))
        if value
    ]
    audit["touched_column_audit"].update(
        {
            "status": "fail",
            "touched_roots": sorted({column.split(":", 1)[0] for column in touched_columns}),
            "touched_columns": touched_columns,
            "unchanged_non_h_columns": False,
        }
    )
    head_patch = _head_patch_fixture()
    for mode in runner.HEAD_PATCH_REQUIRED_MODES:
        head_patch[mode]["per_seed_before_after_metrics"][0]["audit"] = audit
    head_patch["protocol_checks"]["column_audited"] = False
    head_patch["causal_patch_claim"] = runner._head_patch_causal_claim(head_patch)

    aggregate = _aggregate()
    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(
        aggregate,
        _residualized_fixture(aggregate),
        _score_margin_fixture("not_score_margin_sufficient"),
        "head_causal_patch",
        head_patch=head_patch,
    )

    assert a4_hardgates["gates"]["head_causal_patch"]["evidence"]["protocol_checks"]["column_audited"] is False
    assert d5_m["failed_gate"] == "head_causal_patch"


def test_residualization_guards_are_finite_deterministic_and_remove_score_margin_correlation():
    surface = {
        "feature_columns": ["h:0", "h:1", "score:a", "margin:a", "transition_delta:a", "quality:q"],
        "features": np.array(
            [
                [1.0, 3.0, 0.1, 0.9, 0.0, 1.0],
                [2.0, 5.0, 0.2, 0.7, 0.1, 1.0],
                [3.0, 7.0, 0.3, 0.8, 0.0, 1.0],
                [4.0, 9.0, 0.4, 0.4, 0.1, 1.0],
                [5.0, 11.0, 0.5, 0.6, 0.0, 1.0],
            ],
            dtype=np.float64,
        ),
    }

    residual_a, meta_a = runner._residualized_h_against_score_margin(surface)
    residual_b, meta_b = runner._residualized_h_against_score_margin(surface)

    np.testing.assert_allclose(residual_a, residual_b)
    assert meta_a == meta_b
    assert meta_a["finite_values"] is True
    assert meta_a["rank_guard"] == "pass"
    assert meta_a["condition_number_guard"] == "pass"
    assert meta_a["correlation_removal"] == "pass"
    assert meta_a["max_abs_corr_after"] <= meta_a["max_abs_corr_before"]


def test_a4_case_c_is_only_d5_m_candidate():
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, _head_patch_fixture())
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)

    assert hardgates["status"] == "pass"
    assert hardgates["gates"]["A1-HG6"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG5"]["status"] == "pass"
    assert case["case"] == "Case C"
    assert runner._d5_m(hardgates, a4_hardgates)["passed"] is True


def test_case_b_score_margin_sufficiency_blocks_d5_m_even_when_residualized_full_is_strong():
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("score_margin_sufficient")
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, _head_patch_fixture())
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)

    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG5"]["status"] == "fail"
    assert case["case"] == "Case B"
    assert case["failed_gate"] == "A4-HG5"
    assert runner._d5_m(hardgates, a4_hardgates)["passed"] is False


def test_case_a_residualized_collapse_blocks_d5_m():
    aggregate = _aggregate(full_residualized_against_score_margin=(0.50, -0.01))
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, _head_patch_fixture())
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)

    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "fail"
    assert case["case"] == "Case A"
    assert runner._d5_m(hardgates, a4_hardgates)["passed"] is False


def _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, failed_gate, head_patch=None):
    hardgates = runner._a1_hardgates(aggregate)
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, _head_patch_fixture() if head_patch is None else head_patch)
    d5_m = runner._d5_m(hardgates, a4_hardgates)

    assert hardgates["gates"]["A1-HG6"]["status"] == "pass"
    assert a4_hardgates["gates"][failed_gate]["status"] == "fail"
    assert d5_m["passed"] is False
    assert d5_m["status"] == "blocked"
    return a4_hardgates, d5_m


def test_a4_hg1_residualized_status_failure_blocks_d5_m():
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate, status="fail")
    score_margin = _score_margin_fixture("not_score_margin_sufficient")

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, "A4-HG1")

    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG4"]["status"] == "pass"
    assert d5_m["failed_gate"] == "A4-HG1"


def test_a4_hg3_full_without_score_margin_ci_failure_blocks_d5_m():
    aggregate = _aggregate(full_without_score_and_margin=(0.50, -0.01))
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, "A4-HG3")

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG4"]["status"] == "pass"
    assert d5_m["failed_gate"] == "A4-HG3"


def test_a4_hg4_score_margin_status_failure_blocks_d5_m():
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient", status="fail")

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, "A4-HG4")

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert d5_m["failed_gate"] == "A4-HG4"


def test_head_causal_patch_failure_blocks_d5_m():
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    head_patch = _head_patch_fixture(gate_status="fail", auroc_delta=-0.005)

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(
        aggregate,
        residualized,
        score_margin,
        "head_causal_patch",
        head_patch=head_patch,
    )

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG4"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG5"]["status"] == "fail"
    assert d5_m["failed_gate"] == "head_causal_patch"


def test_a4_hg4_unknown_channel_classification_blocks_d5_m():
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("shortcut_unknown")

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, "A4-HG4")

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert d5_m["failed_gate"] == "A4-HG4"


@pytest.mark.parametrize(
    ("cell", "missing"),
    [
        ("present", True),
        ("present", False),
        ("deterministic", True),
        ("deterministic", False),
        ("finite", True),
        ("finite", False),
        ("seed_paired", True),
        ("seed_paired", False),
        ("column_audited", True),
        ("column_audited", False),
        ("classified", True),
        ("classified", False),
    ],
)
def test_a4_hg4_protocol_check_cell_failure_blocks_d5_m(cell, missing):
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    if missing:
        score_margin["protocol_checks"].pop(cell)
    else:
        score_margin["protocol_checks"][cell] = False

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(aggregate, residualized, score_margin, "A4-HG4")

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG4"]["evidence"]["protocol_checks"].get(cell) is (None if missing else False)
    assert d5_m["failed_gate"] == "A4-HG4"


@pytest.mark.parametrize(
    ("classification", "expected_hg5"),
    [
        ("not_score_margin_sufficient", "pass"),
        ("score_margin_sufficient", "fail"),
        ("inconclusive", "fail"),
    ],
)
def test_a4_hg5_channel_classification_paths(classification, expected_hg5):
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    a4_hardgates = runner._a4_hardgates(aggregate, _residualized_fixture(aggregate), _score_margin_fixture(classification), _head_patch_fixture())

    assert a4_hardgates["gates"]["A4-HG1"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG4"]["status"] == "pass"
    assert a4_hardgates["gates"]["A4-HG5"]["status"] == expected_hg5
    assert runner._d5_m(hardgates, a4_hardgates)["passed"] is (expected_hg5 == "pass")


def test_residualized_attribution_claim_has_exact_slot_set_and_arm_mapping():
    aggregate = _aggregate()
    claim = _residualized_claim_fixture(aggregate)

    assert set(claim["slot_order"]) == {
        "full",
        "score_plus_margin",
        "full_residualized",
        "h_only",
        "h_normalized",
        "h_norm_only",
        "full_without_score",
        "margin",
    }
    assert {
        (slot["slot"], slot["source_arm"])
        for slot in claim["slots"]
    } == set(runner.RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS)
    assert dict(runner.RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS)["full_residualized"] == "full_residualized_against_score_margin"


def test_residualized_attribution_claim_metric_pointers_resolve_after_committed_round_trip_shape():
    aggregate = _aggregate()
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("not_score_margin_sufficient")
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, _head_patch_fixture())
    claim = runner._residualized_attribution_claim(aggregate, residualized, score_margin, a4_hardgates)
    payload = {
        "aggregate": aggregate,
        "residualized_attribution": residualized,
        "residualized_attribution_claim": claim,
        "e_hardgates": runner._e_hardgates(aggregate, claim),
    }
    payload["e_hardgates"] = runner._finalize_e_hardgates(payload)

    pointers = runner._residualized_claim_pointers(claim)

    assert pointers
    assert all(_artifact_pointer_resolves(payload, pointer) for pointer in pointers)
    assert runner.validate_residualized_attribution_claim(payload) == []
    assert payload["e_hardgates"]["gates"]["E-HG2_pointer_resolution"]["status"] == "pass"
    assert payload["e_hardgates"]["gates"]["E-HG6_committed_round_trip"]["status"] == "pass"


def test_head_channel_patch_claim_pointer_slots_resolve_after_committed_round_trip_shape():
    head_patch = _head_patch_fixture()
    payload = {"head_channel_patch_evidence": head_patch}
    payload["head_channel_patch_evidence"] = runner._finalize_head_channel_patch_evidence(payload)
    claim = payload["head_channel_patch_evidence"]["causal_patch_claim"]

    assert claim["status"] == "pass"
    assert claim["h_causal_supported"] is True
    assert set(claim["mode_slots_present"]) == set(runner.HEAD_PATCH_REQUIRED_MODES)
    assert all(claim["mode_slots_present"].values())
    assert runner.validate_head_channel_patch_evidence(payload) == []
    assert {
        row["slot"]
        for row in claim["pointer_slots"]
    } == {
        "null_head_arm",
        "null_head_auroc_delta_ci_high",
        "null_head_touched_column_audit",
        "permute_head_rows_arm",
        "permute_head_rows_auroc_delta_ci_high",
        "permute_head_rows_touched_column_audit",
        "paired_deltas",
        "gate_status",
    }
    assert all(_artifact_pointer_resolves(payload, row["source_pointer"]) for row in claim["pointer_slots"])


def test_a4_head_causal_patch_gate_uses_pointer_to_canonical_claim():
    aggregate = _aggregate()
    head_patch = _head_patch_fixture()
    payload = {"head_channel_patch_evidence": head_patch}
    payload["head_channel_patch_evidence"] = runner._finalize_head_channel_patch_evidence(payload)
    a4_hardgates = runner._a4_hardgates(
        aggregate,
        _residualized_fixture(aggregate),
        _score_margin_fixture("not_score_margin_sufficient"),
        payload["head_channel_patch_evidence"],
    )
    evidence = a4_hardgates["gates"]["head_causal_patch"]["evidence"]

    assert a4_hardgates["gates"]["head_causal_patch"]["status"] == "pass"
    assert "causal_patch_claim" not in evidence
    assert evidence["causal_patch_claim_pointer"] == (
        "reports/canonical/gap_head_attribution_capsule.json:"
        "$.head_channel_patch_evidence.causal_patch_claim"
    )
    assert evidence["causal_patch_claim_pointer_resolved"] is True
    assert _artifact_pointer_resolves(payload, evidence["causal_patch_claim_pointer"])
    assert runner._resolve_artifact_pointer_in_capsule(
        payload,
        evidence["causal_patch_claim_pointer"],
    ) == payload["head_channel_patch_evidence"]["causal_patch_claim"]


def test_head_channel_patch_required_variant_missing_fails_closed_and_blocks_d5_m():
    aggregate = _aggregate()
    head_patch = _head_patch_fixture()
    head_patch.pop("permute_head_rows")
    head_patch["protocol_checks"]["required_modes_present"] = False
    head_patch["causal_patch_claim"] = runner._head_patch_causal_claim(head_patch)
    payload = {"head_channel_patch_evidence": head_patch}
    payload["head_channel_patch_evidence"] = runner._finalize_head_channel_patch_evidence(payload)

    assert payload["head_channel_patch_evidence"]["gate_status"] == "fail"
    assert payload["head_channel_patch_evidence"]["causal_patch_claim"]["h_causal_supported"] is False
    assert runner.validate_head_channel_patch_evidence(payload)

    a4_hardgates, d5_m = _assert_a4_gate_blocks_d5_m(
        aggregate,
        _residualized_fixture(aggregate),
        _score_margin_fixture("not_score_margin_sufficient"),
        "head_causal_patch",
        head_patch=payload["head_channel_patch_evidence"],
    )

    assert a4_hardgates["gates"]["A4-HG5"]["status"] == "fail"
    assert d5_m["failed_gate"] == "head_causal_patch"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda claim: claim.update({"terminal_verdict": "positive"}),
        lambda claim: claim.update({"source": ".refactor-loop/host.env"}),
        lambda claim: claim.update({"candidate_body": {"status": "present"}}),
        lambda claim: claim.update({"per_seed_before_after_metrics": []}),
        lambda claim: claim["pointer_slots"][0].update({"ci_summaries": {"AUROC_after_minus_before": {"mean": -0.1}}}),
    ],
)
def test_head_channel_patch_claim_forbidden_key_audit_fails_closed(mutate):
    head_patch = _head_patch_fixture()
    claim = runner._head_patch_causal_claim(head_patch)
    mutate(claim)
    head_patch["causal_patch_claim"] = claim
    payload = {"head_channel_patch_evidence": head_patch}

    failures = runner.validate_head_channel_patch_evidence(payload)

    assert failures
    assert "forbidden paths" in " ".join(failures)


def test_e_hardgates_missing_slot_fails_closed():
    aggregate = _aggregate()
    claim = _residualized_claim_fixture(aggregate)
    claim["slots"] = claim["slots"][:-1]

    e_hardgates = runner._e_hardgates(aggregate, claim)

    assert e_hardgates["status"] == "fail"
    assert e_hardgates["gates"]["E-HG1_slot_set"]["status"] == "fail"
    assert e_hardgates["gates"]["E-HG4_non_score_mechanism_claim_fail_closed"]["status"] == "fail"


def test_e_hardgates_fail_closed_when_residualized_full_does_not_beat_matched_random():
    aggregate = _aggregate(
        full_residualized_against_score_margin=(0.50, 0.01),
        matched_random=(0.60, 0.02),
    )
    claim = _residualized_claim_fixture(aggregate)
    e_hardgates = runner._e_hardgates(aggregate, claim)

    assert claim["non_score_mechanism_claim_allowed"] is False
    assert e_hardgates["gates"]["E-HG3_residualized_full_vs_matched_random"]["status"] == "fail"
    assert e_hardgates["gates"]["E-HG4_non_score_mechanism_claim_fail_closed"]["status"] == "fail"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda claim: claim.update({"terminal_verdict": "positive"}),
        lambda claim: claim.update({"claim_verdict": "positive"}),
        lambda claim: claim.update({"source": ".refactor-loop/host.env"}),
        lambda claim: claim.update({"candidate_body": {"status": "present"}}),
        lambda claim: claim.update({"records": []}),
        lambda claim: claim.update({"raw_payload": {"status": "present"}}),
    ],
)
def test_residualized_claim_forbidden_key_audit_fails_closed(mutate):
    aggregate = _aggregate()
    claim = _residualized_claim_fixture(aggregate)
    mutate(claim)

    e_hardgates = runner._e_hardgates(aggregate, claim)

    assert e_hardgates["gates"]["E-HG5_forbidden_key_audit"]["status"] == "fail"
    assert runner.validate_residualized_attribution_claim(
        {
            "aggregate": aggregate,
            "residualized_attribution": _residualized_fixture(aggregate),
            "residualized_attribution_claim": claim,
            "e_hardgates": e_hardgates,
        }
    )


def test_hg5_never_claims_transition_when_full_without_transition_matches_full():
    aggregate = _aggregate(full_without_transition=(0.86, 0.40))
    hardgates = runner._a1_hardgates(aggregate)
    hg5 = hardgates["gates"]["A1-HG5"]

    assert hg5["status"] == "pass"
    assert hg5["evidence"]["transition_mechanism_claimed"] is False
    assert hg5["evidence"]["transition_not_claimed_due_to_no_difference"] is True


def test_claim_capsule_schema_cc_hardgates_and_d5_axes():
    generated_at = "2026-01-02T03:04:05+00:00"
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("score_margin_sufficient")
    head_patch = _head_patch_fixture()
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, head_patch)
    residualized_claim = runner._residualized_attribution_claim(aggregate, residualized, score_margin, a4_hardgates)
    e_hardgates = runner._e_hardgates(aggregate, residualized_claim)
    d5_m = runner._d5_m(hardgates, a4_hardgates)
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)
    d5_o = runner._d5_o(aggregate, _readiness_ledger())
    mechanism_evidence = runner._mechanism_evidence(d5_o, d5_m, case, a4_hardgates, residualized, score_margin, head_patch)
    capsule = {
        "schema_id": runner.SCHEMA_ID,
        "source_issue": 692,
        "source_issues": [692, 747, 750],
        "artifact_id": runner.ARTIFACT_ID,
        "run_id": "fixture",
        "d5_o": d5_o,
        "d5_m": d5_m,
        "mechanism_case": case,
        "mechanism_evidence": mechanism_evidence,
        "not_implemented": list(runner.NOT_IMPLEMENTED),
        "ledger_debt": runner._ledger_debt(mechanism_evidence),
        "hardgates": hardgates,
        "residualized_attribution": residualized,
        "residualized_attribution_claim": residualized_claim,
        "e_hardgates": e_hardgates,
        "score_margin_causal_evidence": score_margin,
        "head_channel_patch_evidence": head_patch,
        "a4_hardgates": a4_hardgates,
        "claim_capsule_hardgates": {},
        "cost_protocol_pointer": "$.source_artifacts.cost_protocol",
        "control_pointer": runner._control_pointer(),
        "control_evidence": runner._control_evidence(aggregate),
        "scope_seal": runner._scope_seal(),
        "forbidden_column_audit": runner._forbidden_column_audit({arm: ["h:0"] for arm in runner.ARM_NAMES}),
        "failed_gate": d5_m["failed_gate"],
        "what_was_learned": case["what_was_learned"],
        "revocation_ledger": runner._revocation_ledger(hardgates, generated_at, d5_m),
        "positive_discovery_inputs": [],
        "scope": {"not_claimed": list(runner.NOT_CLAIMED)},
        "source_artifacts": {
            "cost_protocol": {
                "status": "recorded",
                "surface_protocol": {
                    "surface_helper": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
                },
            },
        },
    }
    capsule["claim_capsule_hardgates"] = runner._claim_capsule_hardgates(capsule)

    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["source_issue"] == 692
    assert capsule["source_issues"] == [692, 747, 750]
    assert capsule["d5_o"]["status"] == "ready"
    assert capsule["d5_m"]["status"] == "blocked"
    assert capsule["mechanism_evidence"]["evidence_level"] == "patch"
    assert capsule["mechanism_evidence"]["base_level"] == "D5-O"
    assert capsule["mechanism_evidence"]["mechanism_level"] == "blocked"
    assert capsule["mechanism_evidence"]["candidate_mechanism"] == "probe-margin-channel"
    assert capsule["mechanism_evidence"]["required_gate_pointers"] == [
        "$.a4_hardgates.gates.A4-HG2.status",
        "$.a4_hardgates.gates.A4-HG3.status",
        "$.a4_hardgates.gates.head_causal_patch.status",
        "$.a4_hardgates.gates.A4-HG5.status",
    ]
    assert set(capsule["mechanism_evidence"]["metric_pointers"]) >= {
        "residualized_status",
        "score_margin_channel_classification",
        "shuffle_score_margin_delta",
        "replacement_control_delta",
        "head_patch_status",
        "head_patch_delta",
    }
    assert capsule["mechanism_evidence"]["head_patch_status"] == "pass"
    assert capsule["mechanism_evidence"]["source_issue"] == 750
    assert capsule["mechanism_evidence"]["source_issues"] == [747, 750]
    assert _pointer_resolves(capsule, "$.mechanism_evidence.evidence_level")
    assert capsule["residualized_attribution_claim"]["source_artifact"] == runner.CANONICAL_JSON_ARTIFACT
    assert capsule["e_hardgates"]["gates"]["E-HG4_non_score_mechanism_claim_fail_closed"]["status"] == "fail"
    assert set(capsule["not_implemented"]) == {"nonlinear_residualization", "full_causal_replacement_scope"}
    assert capsule["ledger_debt"]
    assert all(row["status"] == "pass" for row in capsule["claim_capsule_hardgates"].values())
    assert {f"CC-HG{index}" for index in range(1, 8)} == set(capsule["claim_capsule_hardgates"])
    resolved = _resolve_pointer(capsule, capsule["cost_protocol_pointer"])
    assert resolved["status"] == "recorded"
    assert resolved["surface_protocol"]["surface_helper"].endswith("::_surface_for_seed")
    for control_arm, control_pointer in capsule["control_pointer"].items():
        assert _resolve_pointer(capsule, control_pointer) == capsule["control_evidence"][control_arm]
    assert capsule["forbidden_column_audit"]["status"] == "pass"
    assert set(runner.NOT_CLAIMED).issubset(set(capsule["scope"]["not_claimed"]))
    assert capsule["revocation_ledger"][0]["failed_gate"] == "A4-HG5"


def test_gap_head_attribution_d5_o_blocks_on_ablation_fail():
    aggregate = _aggregate()
    d5_o = runner._d5_o(aggregate, _readiness_ledger(ablation_status="fail"))

    assert d5_o["status"] == "blocked"
    assert "ablation" in d5_o["failed_checks"]
    assert d5_o["criterion_pointers"]["ablation"] == "reports/canonical/gap-head-ablation.json:$.hardgate.status"
    assert d5_o["readiness"]["ablation"]["status"] == "failed"


def test_gap_head_attribution_d5_o_ready_on_all_pass():
    aggregate = _aggregate()
    d5_o = runner._d5_o(aggregate, _readiness_ledger())

    assert d5_o["status"] == "ready"
    assert d5_o["failed_checks"] == []


def test_gap_head_attribution_mechanism_evidence_does_not_claim_base_level_when_blocked():
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    residualized = _residualized_fixture(aggregate)
    score_margin = _score_margin_fixture("score_margin_sufficient")
    head_patch = _head_patch_fixture()
    a4_hardgates = runner._a4_hardgates(aggregate, residualized, score_margin, head_patch)
    d5_m = runner._d5_m(hardgates, a4_hardgates)
    case = runner._mechanism_case(aggregate, hardgates, a4_hardgates, score_margin)
    d5_o = runner._d5_o(aggregate, _readiness_ledger(ablation_status="fail"))

    mechanism_evidence = runner._mechanism_evidence(
        d5_o,
        d5_m,
        case,
        a4_hardgates,
        residualized,
        score_margin,
        head_patch,
    )

    assert mechanism_evidence["base_status"] == "blocked"
    assert mechanism_evidence["base_level"] == "blocked"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda capsule: capsule.pop("cost_protocol_pointer"),
        lambda capsule: capsule.update({"cost_protocol_pointer": "$.source_artifacts.missing_cost_protocol"}),
    ],
)
def test_claim_capsule_cc_hg6_fails_for_missing_or_dangling_cost_pointer(mutate):
    capsule = {
        "schema_id": runner.SCHEMA_ID,
        "artifact_id": runner.ARTIFACT_ID,
        "control_pointer": runner._control_pointer(),
        "control_evidence": runner._control_evidence(_aggregate()),
        "d5_m": {"passed": False},
        "failed_gate": "A1-HG3",
        "what_was_learned": {"status": "blocked"},
        "revocation_ledger": [{"event": "claim-demotion"}],
        "forbidden_column_audit": {"status": "pass"},
        "scope_seal": {"status": "sealed"},
        "positive_discovery_inputs": [],
        "cost_protocol_pointer": "$.source_artifacts.cost_protocol",
        "source_artifacts": {"cost_protocol": {"status": "recorded"}},
    }
    mutate(capsule)

    gates = runner._claim_capsule_hardgates(capsule)

    assert gates["CC-HG6"]["status"] == "fail"


@pytest.mark.parametrize(
    ("pointer", "expected_status"),
    [
        ("$.source_artifacts.cost_protocol", "pass"),
        ("$.source_artifacts.missing_cost_protocol", "fail"),
    ],
)
def test_write_artifacts_emits_capsule_with_resolvable_cost_pointer_state(tmp_path, pointer, expected_status):
    payload = _artifact_payload(pointer)

    runner._write_artifacts(payload, tmp_path / "run", canonical=False)

    capsule = json.loads((tmp_path / "run" / "claim_capsule.json").read_text(encoding="utf-8"))
    resolves = _pointer_resolves(capsule, capsule["cost_protocol_pointer"])
    assert resolves is (expected_status == "pass")
    assert capsule["claim_capsule_hardgates"]["CC-HG6"]["status"] == expected_status
    assert capsule["claim_capsule_hardgates"]["CC-HG6"]["status"] == ("pass" if resolves else "fail")


@pytest.mark.parametrize(
    ("pointer", "expected_status"),
    [
        ("$.source_artifacts.cost_protocol", "pass"),
        ("$.source_artifacts.missing_cost_protocol", "fail"),
    ],
)
def test_write_artifacts_emits_summary_with_resolvable_cost_pointer_state(tmp_path, pointer, expected_status):
    payload = _artifact_payload(pointer)

    runner._write_artifacts(payload, tmp_path / "run", canonical=False)

    summary = json.loads((tmp_path / "run" / "summary.json").read_text(encoding="utf-8"))
    resolves = _pointer_resolves(summary, summary["cost_protocol_pointer"])
    assert resolves is (expected_status == "pass")
    assert summary["claim_capsule_hardgates"]["CC-HG6"]["status"] == expected_status
    assert summary["claim_capsule_hardgates"]["CC-HG6"]["status"] == ("pass" if resolves else "fail")


def test_a1_run_local_negative_witness_records_a1_hg3_failure(tmp_path):
    artifacts = _write_a1_canonical_negative_witness_artifacts(tmp_path)
    capsule = artifacts["claim_capsule"]
    row = capsule["run_local"]["negative_witness"][0]

    assert row == A1_CANONICAL_NEGATIVE_WITNESS_ROW
    assert list(row) == list(runner.A1_NEGATIVE_WITNESS_KEYS)
    assert capsule["run_local"]["negative_witness_hardgates"]["status"] == "pass"
    assert set(capsule["run_local"]["negative_witness_hardgates"]["gates"]) == {
        "NW-HG1",
        "NW-HG2",
        "NW-HG3",
        "NW-HG4",
        "NW-HG5",
    }


def test_a1_run_local_negative_witness_source_and_evidence_pointers_resolve(tmp_path):
    artifacts = _write_a1_canonical_negative_witness_artifacts(tmp_path)
    capsule = artifacts["claim_capsule"]
    row = capsule["run_local"]["negative_witness"][0]
    source = pointer_value(capsule, row["source_pointer"])
    evidence = pointer_value(capsule, row["evidence_pointer"])

    assert row["source_artifact"] == "reports/runs/a1-canonical/claim_capsule.json"
    assert source == capsule["hardgates"]["gates"]["A1-HG3"]
    assert evidence == capsule["hardgates"]["gates"]["A1-HG3"]
    assert evidence["status"] == "fail"
    assert evidence["evidence"]["full_ci_low"] < evidence["evidence"]["score_plus_margin_ci_high"]
    assert capsule["run_local"]["negative_witness_hardgates"]["gates"]["NW-HG2"]["status"] == "pass"
    assert capsule["run_local"]["negative_witness_hardgates"]["gates"]["NW-HG3"]["status"] == "pass"


def test_a1_negative_witness_public_surfaces_are_pointer_only(tmp_path):
    artifacts = _write_a1_canonical_negative_witness_artifacts(tmp_path)
    public_artifacts = _write_a1_canonical_negative_witness_artifacts(tmp_path, canonical=True)
    owner_ref = {
        "artifact": "reports/runs/a1-canonical/claim_capsule.json",
        "pointer": "$.run_local.negative_witness[0]",
    }
    hardgates_ref = {
        "artifact": "reports/runs/a1-canonical/claim_capsule.json",
        "pointer": "$.run_local.negative_witness_hardgates",
    }
    forbidden = {"witness_id", "bedc_gap_field", "demotion_rule", "reason", "criterion", "terminal_verdict"}

    assert artifacts["claim_capsule"]["run_local"]["negative_witness"] == [A1_CANONICAL_NEGATIVE_WITNESS_ROW]
    for public in (public_artifacts["summary"], public_artifacts["canonical"]):
        assert public["negative_witness"] == [owner_ref]
        assert public["negative_witness_hardgates"] == hardgates_ref
        assert set(public["negative_witness"][0]) == {"artifact", "pointer"}
        surface = json.dumps(
            {
                "negative_witness": public["negative_witness"],
                "negative_witness_hardgates": public["negative_witness_hardgates"],
            },
            sort_keys=True,
        )
        assert not any(term in surface for term in forbidden)
    assert not any(term in public_artifacts["report"] for term in forbidden)


def test_a1_negative_witness_fail_closed_on_dangling_pointer(tmp_path):
    payload = _a1_canonical_negative_witness_payload()
    payload["hardgates"]["gates"].pop("A1-HG3")
    run_dir = tmp_path / "reports/runs/a1-canonical"

    runner._write_artifacts(payload, run_dir, canonical=False)

    capsule = json.loads((run_dir / "claim_capsule.json").read_text(encoding="utf-8"))
    row = capsule["run_local"]["negative_witness"][0]
    gates = capsule["run_local"]["negative_witness_hardgates"]["gates"]

    assert row["status"] == "blocked"
    assert row["witness_id"] == A1_CANONICAL_NEGATIVE_WITNESS_ROW["witness_id"]
    assert list(row) == list(runner.A1_NEGATIVE_WITNESS_KEYS)
    assert capsule["run_local"]["negative_witness_hardgates"]["status"] == "fail"
    assert gates["NW-HG2"]["status"] == "fail"
    assert gates["NW-HG3"]["status"] == "fail"
    assert capsule["d5_m"]["status"] == "blocked"
    assert capsule["d5_m"]["failed_gate"] == "A1-HG3"

    old_root = runner.ROOT
    try:
        runner.ROOT = tmp_path
        row = runner._a1_negative_witness_row(
            "reports/runs/a1-canonical/claim_capsule.json",
            _a1_canonical_negative_witness_payload(),
        )
        row["regression_test"] = "tests/test_gap_head_attribution_capsule.py::missing_negative_witness_test"
        run_local = {"negative_witness": [row]}
        probe = {**_a1_canonical_negative_witness_payload(), "run_local": run_local}
        hardgates = runner._a1_negative_witness_hardgates(probe, row)
    finally:
        runner.ROOT = old_root

    assert hardgates["status"] == "fail"
    assert hardgates["gates"]["NW-HG4"]["status"] == "fail"


def test_a1_negative_witness_has_no_terminal_verdict_leakage(tmp_path):
    artifacts = _write_a1_canonical_negative_witness_artifacts(tmp_path)
    run_local = artifacts["claim_capsule"]["run_local"]

    assert not _contains_key(
        {
            "negative_witness": run_local["negative_witness"],
            "negative_witness_hardgates": run_local["negative_witness_hardgates"],
        },
        "terminal_verdict",
    )

    row = dict(run_local["negative_witness"][0])
    row["terminal_verdict"] = "leak"
    probe = {**artifacts["claim_capsule"], "run_local": {"negative_witness": [row]}}
    hardgates = runner._a1_negative_witness_hardgates(probe, row)

    assert hardgates["status"] == "fail"
    assert hardgates["gates"]["NW-HG5"]["status"] == "fail"


def test_write_artifacts_emits_all_local_pointers_resolvable_in_persisted_json(tmp_path):
    old_root = runner.ROOT
    payload = _artifact_payload()
    run_dir = tmp_path / "run"

    try:
        runner.ROOT = tmp_path
        _write_readiness_context(tmp_path)
        _write_readiness_context(_lab_root_for_artifact(run_dir / "claim_capsule.json"))
        runner._write_artifacts(payload, run_dir, canonical=True)
    finally:
        runner.ROOT = old_root

    artifacts = (
        run_dir / "claim_capsule.json",
        run_dir / "summary.json",
        tmp_path / runner.CANONICAL_JSON_ARTIFACT,
    )
    for artifact in artifacts:
        doc = json.loads(artifact.read_text(encoding="utf-8"))
        pointers = _collect_pointers(doc)
        assert pointers
        dangling = []
        for pointer_path, pointer in pointers:
            target = _pointer_target_payload(artifact, doc, pointer_path)
            if not _pointer_resolves(target, pointer):
                dangling.append((pointer_path, pointer))
        assert dangling == []
        assert all(
            pointer.startswith("$.control_evidence.")
            for path, pointer in pointers
            if path.startswith("$.control_pointer.")
        )


def test_recursive_pointer_walker_rejects_dangling_pointer_fixture():
    doc = {
        "control_pointer": {
            "group": {
                "matched_random": "$.nonexistent.node",
            },
        },
        "control_evidence": {"matched_random": {"status": "recorded"}},
    }

    dangling = [(path, pointer) for path, pointer in _collect_pointers(doc) if not _pointer_resolves(doc, pointer)]

    assert dangling == [("$.control_pointer.group.matched_random", "$.nonexistent.node")]


def test_recursive_pointer_walker_rejects_dangling_nested_pointer_value_fixture():
    doc = {
        "evidence_pointer": {
            "outer": [
                {
                    "inner": "$.missing.deep.node",
                }
            ],
        },
        "evidence": {"status": "recorded"},
    }

    dangling = [(path, pointer) for path, pointer in _collect_pointers(doc) if not _pointer_resolves(doc, pointer)]

    assert dangling == [("$.evidence_pointer.outer.0.inner", "$.missing.deep.node")]


def test_claim_capsule_persisted_json_artifacts_have_resolvable_pointer_fields():
    root = Path(__file__).resolve().parents[1]
    artifacts = [root / runner.CANONICAL_JSON_ARTIFACT]
    artifacts.extend(sorted((root / "reports" / "runs").glob("*/claim_capsule.json")))
    artifacts.extend(sorted((root / "reports" / "runs").glob("*/summary.json")))
    artifacts = [artifact for artifact in artifacts if artifact.exists()]

    for artifact in artifacts:
        doc = json.loads(artifact.read_text(encoding="utf-8"))
        pointers = _collect_pointers(doc)
        dangling = []
        for pointer_path, pointer in pointers:
            target = _pointer_target_payload(artifact, doc, pointer_path)
            if not _pointer_resolves(target, pointer):
                dangling.append((pointer_path, pointer))
        assert dangling == [], artifact

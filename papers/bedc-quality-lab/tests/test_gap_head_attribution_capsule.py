import json

import numpy as np
import pytest

from scripts.experiment_stats import metric_stats
from scripts import run_gap_head_attribution_capsule as runner


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
    "matched_random",
)


def _stat(value):
    return metric_stats([float(value)] * 4)


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
        "matched_random": (0.51, 0.01),
    }
    values.update(overrides)
    return {
        "record_count": 4 * len(EXPECTED_ARMS),
        "seed_order": [1, 2, 3, 4],
        "arm_order": list(EXPECTED_ARMS),
        "by_arm": {arm: _row(*values[arm]) for arm in EXPECTED_ARMS},
    }


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


def test_a1_hardgates_and_case_one_d5_m():
    aggregate = _aggregate()
    hardgates = runner._a1_hardgates(aggregate)
    case = runner._mechanism_case(aggregate, hardgates)

    assert hardgates["status"] == "pass"
    assert hardgates["gates"]["A1-HG6"]["status"] == "pass"
    assert case["case"] == "Case 1"
    assert runner._d5_m(hardgates)["passed"] is True


def test_case_two_margin_shortcut_blocks_d5_m():
    aggregate = _aggregate(score_plus_margin=(0.86, 0.39))
    hardgates = runner._a1_hardgates(aggregate)
    case = runner._mechanism_case(aggregate, hardgates)

    assert hardgates["gates"]["A1-HG3"]["status"] == "fail"
    assert hardgates["gates"]["A1-HG6"]["status"] == "fail"
    assert case["case"] == "Case 2"
    assert case["failed_gate"] == "A1-HG3"
    assert runner._d5_m(hardgates)["passed"] is False


def test_case_three_norm_shortcut_blocks_d5_m():
    aggregate = _aggregate(h_norm_only=(0.86, 0.39))
    hardgates = runner._a1_hardgates(aggregate)
    case = runner._mechanism_case(aggregate, hardgates)

    assert hardgates["gates"]["A1-HG4"]["status"] == "fail"
    assert case["case"] == "Case 3"
    assert case["failed_gate"] == "A1-HG4"


def test_hg5_never_claims_transition_when_full_without_transition_matches_full():
    aggregate = _aggregate(full_without_transition=(0.86, 0.40))
    hardgates = runner._a1_hardgates(aggregate)
    hg5 = hardgates["gates"]["A1-HG5"]

    assert hg5["status"] == "pass"
    assert hg5["evidence"]["transition_mechanism_claimed"] is False
    assert hg5["evidence"]["transition_not_claimed_due_to_no_difference"] is True


def test_claim_capsule_schema_cc_hardgates_and_d5_axes():
    generated_at = "2026-01-02T03:04:05+00:00"
    aggregate = _aggregate(score_plus_margin=(0.86, 0.39))
    hardgates = runner._a1_hardgates(aggregate)
    case = runner._mechanism_case(aggregate, hardgates)
    capsule = {
        "schema_id": runner.SCHEMA_ID,
        "source_issue": 692,
        "artifact_id": runner.ARTIFACT_ID,
        "run_id": "fixture",
        "d5_o": runner._d5_o(aggregate),
        "d5_m": runner._d5_m(hardgates),
        "mechanism_case": case,
        "hardgates": hardgates,
        "claim_capsule_hardgates": {},
        "cost_protocol_pointer": "$.source_artifacts.source_surface",
        "control_pointer": runner._control_pointer(),
        "scope_seal": runner._scope_seal(),
        "forbidden_column_audit": runner._forbidden_column_audit({arm: ["h:0"] for arm in runner.ARM_NAMES}),
        "failed_gate": "A1-HG3",
        "what_was_learned": case["what_was_learned"],
        "revocation_ledger": runner._revocation_ledger(hardgates, generated_at),
        "positive_discovery_inputs": [],
        "scope": {"not_claimed": list(runner.NOT_CLAIMED)},
    }
    capsule["claim_capsule_hardgates"] = runner._claim_capsule_hardgates(capsule)

    assert capsule["schema_id"] == "bedc.quality.claim_capsule.v1"
    assert capsule["source_issue"] == 692
    assert capsule["d5_o"]["status"] == "ready"
    assert capsule["d5_m"]["status"] == "blocked"
    assert all(row["status"] == "pass" for row in capsule["claim_capsule_hardgates"].values())
    assert {f"CC-HG{index}" for index in range(1, 8)} == set(capsule["claim_capsule_hardgates"])
    assert capsule["forbidden_column_audit"]["status"] == "pass"
    assert set(runner.NOT_CLAIMED).issubset(set(capsule["scope"]["not_claimed"]))
    assert capsule["revocation_ledger"][0]["failed_gate"] == "A1-HG3"

from __future__ import annotations

import json

import numpy as np
import pytest

from bedc_quality_lab.mg_cap_tournament import (
    ArmSpec,
    BootstrapSummary,
    Episode,
    SequenceSampler,
    TournamentConfig,
    bootstrap_mean_ci,
    gate_and_verdict,
    make_arm_specs,
    mission_tokens,
    parameter_match_status,
    write_report_markdown,
    _last_valid,
    _partial_observation_action_mask,
)


def test_mission_tokens_are_fixed_width_and_content_based() -> None:
    tokens = mission_tokens("use the key", max_length=6)

    assert tokens.shape == (6,)
    assert int(tokens[0]) != 0
    assert int(tokens[-1]) == 0
    assert mission_tokens("use the key", max_length=4).tolist() == mission_tokens("use the key", max_length=4).tolist()


def test_bootstrap_mean_ci_contains_mean_for_binary_successes() -> None:
    summary = bootstrap_mean_ci(np.asarray([1, 1, 0, 1, 0], dtype=np.float32), seed=7, resamples=256)

    assert isinstance(summary, BootstrapSummary)
    assert summary.mean == 0.6
    assert 0.0 <= summary.ci_low <= summary.mean <= summary.ci_high <= 1.0


def test_arm_specs_are_parameter_matched() -> None:
    specs = make_arm_specs(hidden_dim=32)
    baseline_specs = [spec for spec in specs if spec.priority == 1]

    assert {spec.name for spec in baseline_specs} == {"GRU_base", "Transformer_base"}
    assert parameter_match_status(baseline_specs)["status"] == "pass"


def test_sequence_sampler_can_balance_rare_actions() -> None:
    episode = Episode(
        images=np.zeros((100, 7, 7, 3), dtype=np.int64),
        missions=np.zeros((100, 16), dtype=np.int64),
        actions=np.asarray([2] * 90 + [3] * 5 + [5] * 5, dtype=np.int64),
        oracle_success=True,
        executed_steps=100,
    )
    sampler = SequenceSampler([episode], context_length=4, seed=5, balance_actions=True)

    _, _, _, _, actions = sampler.sample(90)
    counts = {int(action): int(np.sum(actions == action)) for action in np.unique(actions)}

    assert counts[3] >= 20
    assert counts[5] >= 20


def test_last_valid_selects_right_edge_of_left_padded_sequences() -> None:
    torch = pytest.importorskip("torch")
    hidden = torch.arange(2 * 5 * 1, dtype=torch.float32).reshape(2, 5, 1)
    mask = torch.tensor(
        [
            [False, False, False, True, True],
            [False, False, True, True, True],
        ],
        dtype=torch.bool,
    )

    selected = _last_valid(hidden, mask)

    assert selected.reshape(-1).tolist() == [4.0, 9.0]


def test_partial_observation_action_mask_filters_invalid_front_cell_actions() -> None:
    image = np.zeros((7, 7, 3), dtype=np.int64)
    image[3, 5, 0] = 2

    wall_mask = _partial_observation_action_mask(image)

    assert wall_mask[0]
    assert wall_mask[1]
    assert not wall_mask[2]
    assert not wall_mask[3]
    assert not wall_mask[5]

    image[3, 5, 0] = 5
    key_mask = _partial_observation_action_mask(image)
    assert key_mask[3]
    assert not key_mask[2]


def test_gate_and_verdict_requires_ood_primary_not_auxiliary() -> None:
    base_ood_a = [1.0] * 40 + [0.0] * 60
    base_ood_b = [1.0] * 36 + [0.0] * 64
    cand_ood_a = [1.0] * 54 + [0.0] * 46
    cand_ood_b = [1.0] * 50 + [0.0] * 50
    arms = {
        "GRU_base": {
            "priority": 1,
            "selected_by_id_validation": True,
            "splits": {
                "id": {"success": {"mean": 0.84, "ci_low": 0.80, "ci_high": 0.88}},
                "ood_door_key": {
                    "episode_successes": base_ood_a,
                    "success": {"mean": 0.40, "ci_low": 0.34, "ci_high": 0.46},
                },
                "ood_transfer": {
                    "episode_successes": base_ood_b,
                    "success": {"mean": 0.36, "ci_low": 0.30, "ci_high": 0.42},
                },
            },
        },
        "Transformer_base": {
            "priority": 1,
            "selected_by_id_validation": False,
            "splits": {
                "id": {"success": {"mean": 0.82, "ci_low": 0.78, "ci_high": 0.86}},
                "ood_door_key": {"success": {"mean": 0.38, "ci_low": 0.32, "ci_high": 0.44}},
                "ood_transfer": {"success": {"mean": 0.34, "ci_low": 0.28, "ci_high": 0.40}},
            },
        },
        "DGT_BCD": {
            "priority": 2,
            "parameter_match": {"status": "pass"},
            "splits": {
                "id": {"success": {"mean": 0.83, "ci_low": 0.79, "ci_high": 0.87}},
                "ood_door_key": {
                    "episode_successes": cand_ood_a,
                    "success": {"mean": 0.54, "ci_low": 0.48, "ci_high": 0.60},
                },
                "ood_transfer": {
                    "episode_successes": cand_ood_b,
                    "success": {"mean": 0.50, "ci_low": 0.44, "ci_high": 0.56},
                },
            },
        },
    }
    controls = {
        "random_policy": {"success": {"mean": 0.02, "ci_low": 0.0, "ci_high": 0.05}},
        "oracle": {"success": {"mean": 0.98, "ci_low": 0.96, "ci_high": 1.0}},
    }

    result = gate_and_verdict(arms, controls)

    assert result["validity_gate"]["status"] == "pass"
    assert result["best_baseline"]["name"] == "GRU_base"
    assert result["candidates"]["DGT_BCD"]["verdict"] == "true_win"
    assert result["overall_verdict"] == "true_win"


def test_markdown_report_contains_primary_verdict(tmp_path) -> None:
    payload = {
        "schema_id": "bedc-quality-lab:mg-cap-tournament",
        "config": TournamentConfig(
            train_env_id="MiniGrid-DoorKey-8x8-v0",
            ood_env_ids=("MiniGrid-DoorKey-16x16-v0", "MiniGrid-KeyCorridorS3R3-v0"),
            seeds=(0,),
            demo_episodes=8,
            eval_episodes=8,
            train_steps=4,
        ).to_dict(),
        "arms": {},
        "validity_and_verdict": {
            "validity_gate": {"status": "fail", "reasons": ["baseline ID success below 0.80"]},
            "overall_verdict": "invalid",
        },
    }
    path = tmp_path / "report.md"

    write_report_markdown(payload, path)

    text = path.read_text(encoding="utf-8")
    assert "MG-CAP Tournament" in text
    assert "Primary endpoint: OOD episode success" in text
    assert "invalid" in text


def test_arm_spec_payload_is_json_serializable() -> None:
    payload = ArmSpec(name="GRU_base", family="gru", hidden_dim=32, priority=1, parameter_count=123).to_dict()

    assert json.loads(json.dumps(payload))["name"] == "GRU_base"

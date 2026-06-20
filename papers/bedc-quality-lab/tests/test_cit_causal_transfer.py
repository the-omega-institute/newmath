from __future__ import annotations

import pytest


from bedc_quality_lab.cit_causal_transfer import (
    CITConfig,
    analytic_bayes_2afc,
    arm_view,
    bayes_correct_flags,
    bayes_posterior_2afc,
    bootstrap_ci,
    evaluate_probabilities,
    generate_dataset,
    generate_q_dataset,
    run_arm,
    run_fresh_action,
    run_q_arm,
)


def _require_cuda():
    torch = pytest.importorskip("torch")
    if not torch.cuda.is_available():
        pytest.skip("CUDA is unavailable")
    return torch


def test_causal_dataset_encodes_label_as_action_witness_relation():
    rows = generate_dataset(CITConfig(seed=7), n=4)

    assert [row["label"] for row in rows] == [0, 1, 0, 1]
    assert all(row["source"] == "causal" for row in rows)
    assert [row["action"] == row["w"] for row in rows] == [False, True, False, True]


def test_independent_control_breaks_action_witness_label_rule_deterministically():
    config = CITConfig(seed=7, independent_w=True)
    rows = generate_q_dataset(config, n=6, seed_offset=3)

    assert rows == generate_q_dataset(config, n=6, seed_offset=3)
    assert all(row["source"] == "independent_w" for row in rows)
    assert [row["label"] for row in rows] == [0, 1, 0, 1, 0, 1]


def test_q_dataset_rejects_degenerate_source_count():
    with pytest.raises(ValueError, match="q must be at least 2"):
        generate_q_dataset(CITConfig(q=1), n=1)


def test_arm_view_branches_and_invalid_view():
    config = CITConfig(q=3)
    row = {"action": 2, "w": 1, "label": 0, "nuisance": 0.25}

    assert arm_view(row, config, view="action") == [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]
    assert arm_view(row, config, view="witness") == [0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.25]
    assert arm_view(row, config, view="causal") == [0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.25]
    assert arm_view(row, CITConfig(q=3, independent_w=True), view="causal") == [0.0] * 8

    with pytest.raises(ValueError, match="unknown CIT arm view"):
        arm_view(row, config, view="missing")


def test_evaluation_bootstrap_and_bayes_contracts_are_cpu_deterministic():
    evaluation = evaluate_probabilities([0.1, 0.7, 0.5], [0, 1, 0])

    assert evaluation == {"accuracy": pytest.approx(2 / 3), "correct": [1.0, 1.0, 0.0], "count": 3}
    assert bootstrap_ci([], samples=3) == {"mean": 0.0, "lower": 0.0, "upper": 0.0}
    assert bootstrap_ci([1.0, 0.0, 1.0], samples=5, seed=11)["mean"] == pytest.approx(2 / 3)

    causal = CITConfig()
    indifferent = CITConfig(bayes_indifferent=True)
    match_row = {"action": 1, "w": 1, "label": 1}
    miss_row = {"action": 0, "w": 1, "label": 0}

    assert analytic_bayes_2afc(causal) == 1.0
    assert analytic_bayes_2afc(indifferent) == 0.5
    assert bayes_posterior_2afc(match_row, causal) == {"p0": 0.0, "p1": 1.0}
    assert bayes_posterior_2afc(miss_row, causal) == {"p0": 1.0, "p1": 0.0}
    assert bayes_posterior_2afc(match_row, indifferent) == {"p0": 0.5, "p1": 0.5}
    assert bayes_correct_flags([match_row, miss_row], causal) == [1.0, 1.0]


def test_fresh_pooled_shape_uses_lightweight_arm_payloads(monkeypatch):
    import bedc_quality_lab.cit_causal_transfer as cit

    def fake_fresh(config):
        return {"arm": "fresh-action", "learned": {"point": 0.6}, "seed": config.seed}

    def fake_arm(config):
        return {"arm": "causal-transfer", "learned": {"point": 0.8}, "seed": config.seed}

    def fake_q(config):
        return {"arm": "q-source", "learned": {"point": 1.0}, "q": config.q, "seed": config.seed}

    monkeypatch.setattr(cit, "run_fresh_action", fake_fresh)
    monkeypatch.setattr(cit, "run_arm", fake_arm)
    monkeypatch.setattr(cit, "run_q_arm", fake_q)

    result = cit.run_fresh_pooled(CITConfig(seed=20, q=2))

    assert result["arm"] == "fresh-pooled"
    assert [arm["arm"] for arm in result["arms"]] == ["fresh-action", "causal-transfer", "q-source"]
    assert result["arms"][1]["seed"] == 37
    assert result["arms"][2]["q"] == 3
    assert result["learned"] == {"point": pytest.approx(0.8), "min": 0.6, "max": 1.0}


def test_cli_payload_contracts_use_schema_runner_and_config_mapping(monkeypatch, tmp_path):
    from scripts import run_cit_causal_transfer, run_cit_leak_probe, run_cit_stratum, run_cit_verify

    monkeypatch.setattr(run_cit_causal_transfer, "run_arm", lambda config: {"arm": "single", "device": config.device})
    monkeypatch.setattr(run_cit_causal_transfer, "run_fresh_pooled", lambda config: {"arm": "pooled", "hidden": config.hidden_dim})
    monkeypatch.setattr(run_cit_leak_probe, "run_arm", lambda config: {"arm": "leak", "independent": config.independent_w})
    monkeypatch.setattr(run_cit_leak_probe, "run_fresh_action", lambda config: {"arm": "fresh", "bayes": config.bayes_indifferent})
    monkeypatch.setattr(run_cit_stratum, "run_q_arm", lambda config: {"arm": "q", "q": config.q})
    monkeypatch.setattr(run_cit_verify, "run_arm", lambda config: {"arm": "verify", "train_n": config.train_n})
    monkeypatch.setattr(run_cit_verify, "run_fresh_action", lambda config: {"arm": "fresh", "eval_n": config.eval_n})

    causal_args = run_cit_causal_transfer.parse_args(
        ["--result-path", str(tmp_path / "causal.json"), "--device", "cpu", "--hidden-dim", "9", "--pooled"]
    )
    causal_payload = run_cit_causal_transfer.build_payload(causal_args)
    assert causal_payload["schema_id"] == "bedc-quality-lab:cit-causal-transfer"
    assert causal_payload["runner"] == "scripts/run_cit_causal_transfer.py"
    assert causal_payload["result"] == {"arm": "pooled", "hidden": 9}

    leak_args = run_cit_leak_probe.parse_args(["--result-path", str(tmp_path / "leak.json"), "--bayes-indifferent"])
    leak_payload = run_cit_leak_probe.build_payload(leak_args)
    assert leak_payload["schema_id"] == "bedc-quality-lab:cit-leak-probe"
    assert leak_payload["runner"] == "scripts/run_cit_leak_probe.py"
    assert leak_payload["controls"] == [{"arm": "leak", "independent": False}, {"arm": "fresh", "bayes": True}]

    stratum_args = run_cit_stratum.parse_args(["--result-path", str(tmp_path / "stratum.json"), "--q", "5"])
    stratum_payload = run_cit_stratum.build_payload(stratum_args)
    assert stratum_payload["schema_id"] == "bedc-quality-lab:cit-stratum"
    assert stratum_payload["runner"] == "scripts/run_cit_stratum.py"
    assert stratum_payload["result"] == {"arm": "q", "q": 5}

    verify_args = run_cit_verify.parse_args(["--result-path", str(tmp_path / "verify.json"), "--train-n", "17", "--eval-n", "19"])
    verify_payload = run_cit_verify.build_payload(verify_args)
    assert verify_payload["schema_id"] == "bedc-quality-lab:cit-verify"
    assert verify_payload["runner"] == "scripts/run_cit_verify.py"
    assert verify_payload["arms"] == [{"arm": "verify", "train_n": 17}, {"arm": "fresh", "eval_n": 19}]


def test_causal_transfer_main_writes_payload(monkeypatch, tmp_path, capsys):
    from scripts import run_cit_causal_transfer

    monkeypatch.setattr(run_cit_causal_transfer, "run_arm", lambda config: {"arm": "single", "seed": config.seed})
    result_path = tmp_path / "result.json"

    run_cit_causal_transfer.main(["--result-path", str(result_path), "--seed", "33", "--device", "cpu"])

    assert result_path.read_text(encoding="utf-8").strip().startswith("{")
    assert '"seed": 33' in capsys.readouterr().out


def _cuda_config(**overrides):
    base = {
        "seed": 1726,
        "train_n": 192,
        "eval_n": 192,
        "hidden_dim": 12,
        "epochs": 80,
        "batch_size": 64,
        "bootstrap_samples": 80,
        "device": "cuda",
    }
    base.update(overrides)
    return CITConfig(**base)


def test_hard_independent_w_control_ci_covers_chance():
    _require_cuda()
    result = run_fresh_action(_cuda_config(independent_w=True))
    ci = result["learned"]["ci"]

    assert ci["lower"] <= 0.5 <= ci["upper"]
    assert result["analytic_bayes"] == 0.5


def test_bayes_indifferent_learned_ci_covers_chance():
    _require_cuda()
    result = run_arm(_cuda_config(bayes_indifferent=True, seed=1733))
    ci = result["learned"]["ci"]

    assert ci["lower"] <= 0.5 <= ci["upper"]
    assert result["analytic_bayes"] == 0.5


def test_learned_point_is_positive_and_bounded_by_bayes_tolerance():
    _require_cuda()
    result = run_arm(_cuda_config(seed=1741))
    point = result["learned"]["point"]

    assert point > 0.5
    assert point <= result["analytic_bayes"] + 0.02


def test_q3_transfer_is_positive():
    _require_cuda()
    result = run_q_arm(_cuda_config(q=3, seed=1759))

    assert result["config"]["q"] == 3
    assert result["learned"]["point"] > 0.5

import json
import runpy
import sys
from pathlib import Path

import pytest

from bedc_quality_lab.torch_bedc_jepa import (
    ActiveGapLedgerConfig,
    _active_gap_ledger_sampling,
    _active_gap_guardrail,
    run_active_gap_ledger_curriculum,
    run_active_gap_ledger_controlled,
)
from bedc_quality_lab.bedc_jepa_world import make_boundary_gated_batch

ROOT = Path(__file__).resolve().parents[1]


def _small_config(**overrides):
    values = {
        "seed": 101,
        "initial_train_count": 80,
        "pool_count": 180,
        "test_count": 72,
        "active_budget": 45,
        "epochs": 4,
        "gap_auc_floor": 0.0,
        "unlogged_error_ceiling": 1.0,
        "coverage_min_delta": -1.0,
        "latent_r2_min_delta": -1.0,
        "gap_auc_min_delta": -1.0,
    }
    values.update(overrides)
    return ActiveGapLedgerConfig(**values)


def test_active_gap_ledger_curriculum_records_ou_retraining_and_minigrid_boundary():
    packet = run_active_gap_ledger_curriculum(_small_config())

    assert packet["schema_id"] == "bedc-jepa-active-gap-ledger-curriculum"
    assert packet["status"] == "executed"
    assert packet["source"]["name"] == "boundary-gated-ou-world"
    assert packet["source"]["training"] == "torch-active-gap-ledger-curriculum"
    assert packet["source"]["train_count_after_active_sampling"] > packet["source"]["train_count_initial"]
    assert set(packet) >= {
        "schema_id",
        "status",
        "source",
        "thresholds",
        "sampling",
        "metrics_before",
        "metrics_after",
        "deltas",
        "guardrail",
        "minigrid_active_curriculum",
        "cannot_claim",
    }
    assert packet["minigrid_active_curriculum"]["status"] == "not_executed"
    assert any("MiniGrid" in row for row in packet["cannot_claim"])


def test_active_gap_sampling_reasons_are_budgeted_and_mutually_exclusive():
    packet = run_active_gap_ledger_curriculum(_small_config(active_budget=30))
    sampling = packet["sampling"]

    assert sampling["budget"] == 30
    assert sampling["selected"] <= 30
    assert sampling["mutually_exclusive"] is True
    assert sampling["reason_order"] == ["high_gap", "boundary_band", "unlogged_transition"]
    assert set(sampling["reasons"]) == {"high_gap", "boundary_band", "unlogged_transition"}
    all_indices = []
    for reason, row in sampling["reasons"].items():
        assert row["requested"] >= row["selected"]
        assert row["selected"] == len(row["indices"])
        assert reason in {"high_gap", "boundary_band", "unlogged_transition"}
        all_indices.extend(row["indices"])
    assert len(all_indices) == len(set(all_indices))
    assert sampling["selected_indices"] == all_indices


def test_active_gap_sampling_support_anchor_and_scrambled_placebo_are_explicit():
    pool = make_boundary_gated_batch(96, rho=0.84, radius=1.0, gap_width=0.14, seed=909)
    scores = {
        "gap": pool.gap.astype(float) * 0.8 + (~pool.gap).astype(float) * 0.1,
        "distinction": pool.distinction.astype(float),
    }

    selected, sampling = _active_gap_ledger_sampling(
        pool,
        scores,
        active_budget=24,
        arm="coverage_preserving",
        preserve_fraction=0.5,
    )
    support_indices = sampling["reasons"]["support_anchor"]["indices"]

    assert sampling["arm"] == "coverage_preserving"
    assert sampling["reason_order"][0] == "support_anchor"
    assert sampling["mutually_exclusive"] is True
    assert len(selected) <= 24
    assert support_indices
    assert all(not bool(pool.gap[idx]) for idx in support_indices)
    assert all(float(scores["gap"][idx]) < 0.5 for idx in support_indices)

    _, placebo = _active_gap_ledger_sampling(
        pool,
        scores,
        active_budget=24,
        arm="placebo",
    )
    assert placebo["arm"] == "placebo"
    assert placebo["score_source"] == "scrambled_gap"


def test_active_gap_guardrail_fails_closed_when_thresholds_are_unreachable():
    packet = run_active_gap_ledger_curriculum(
        _small_config(
            gap_auc_floor=1.1,
            unlogged_error_ceiling=-0.1,
            coverage_min_delta=1.0,
            latent_r2_min_delta=1.0,
            gap_auc_min_delta=1.0,
        )
    )

    assert packet["status"] == "failed_guardrail"
    assert packet["guardrail"]["passed"] is False
    assert packet["guardrail"]["coverage_expansion_reported"] is False
    assert packet["guardrail"]["reported_coverage_delta"] == 0.0
    assert set(packet["guardrail"]["failures"]) >= {
        "gap_auc_floor",
        "unlogged_error_ceiling",
        "coverage_gate",
    }


def test_active_gap_guardrail_suppresses_coverage_expansion_when_any_gate_fails():
    before = {
        "gap_detection_auc": 0.90,
        "linear_identifiability_r2": 0.80,
        "unlogged_error_rate": 0.01,
        "certified_coverage": 0.40,
        "bedc_debt_score": 0.10,
        "distinction_accuracy_outside_gap": 0.95,
    }
    after = {
        "gap_detection_auc": 0.91,
        "linear_identifiability_r2": 0.82,
        "unlogged_error_rate": 0.01,
        "certified_coverage": 0.50,
        "bedc_debt_score": 0.08,
        "distinction_accuracy_outside_gap": 0.96,
    }
    guardrail = _active_gap_guardrail(
        before,
        after,
        _small_config(gap_auc_floor=0.99, coverage_min_delta=0.01),
    )

    assert guardrail["passed"] is False
    assert guardrail["failures"] == ["gap_auc_floor"]
    assert guardrail["coverage_expansion_reported"] is False
    assert guardrail["reported_coverage_delta"] == 0.0


def test_active_gap_curriculum_accepts_keyword_overrides():
    packet = run_active_gap_ledger_curriculum(
        seed=103,
        initial_train_count=72,
        pool_count=150,
        test_count=64,
        active_budget=24,
        epochs=3,
        gap_auc_floor=0.0,
        unlogged_error_ceiling=1.0,
        coverage_min_delta=-1.0,
        latent_r2_min_delta=-1.0,
        gap_auc_min_delta=-1.0,
    )

    assert packet["source"]["seed"] == 103.0
    assert packet["sampling"]["budget"] == 24
    assert packet["thresholds"]["active_budget"] == 24


def test_active_gap_curriculum_rejects_mixed_config_and_overrides():
    with pytest.raises(ValueError, match="either config or keyword overrides"):
        run_active_gap_ledger_curriculum(_small_config(), active_budget=12)


def test_active_gap_curriculum_rejects_empty_active_budget():
    with pytest.raises(ValueError, match="active_budget must be positive"):
        run_active_gap_ledger_curriculum(_small_config(active_budget=0))


def test_active_gap_controlled_runner_summarizes_three_arms(monkeypatch):
    def fake_arm(config=None, *, arm, preserve_fraction=0.5, **overrides):
        base = {"real": 0.70, "coverage_preserving": 0.72, "placebo": 0.69}[arm]
        before = {
            "gap_detection_auc": 0.68,
            "bedc_debt_score": 0.20,
            "certified_coverage": 0.40,
            "linear_identifiability_r2": 0.80,
            "unlogged_error_rate": 0.03,
            "distinction_accuracy_outside_gap": 0.90,
        }
        after = {
            "gap_detection_auc": base,
            "bedc_debt_score": 0.18,
            "certified_coverage": 0.41,
            "linear_identifiability_r2": 0.798,
            "unlogged_error_rate": 0.02,
            "distinction_accuracy_outside_gap": 0.91,
        }
        deltas = {key: after[key] - before[key] for key in before}
        seed = config.seed if config is not None else overrides["seed"]
        return {
            "status": "executed",
            "source": {"seed": float(seed)},
            "torch_environment": {"resolved_device": "cuda"},
            "sampling": {"arm": arm},
            "guardrail": {"passed": True},
            "metrics_before": before,
            "metrics_after": after,
            "deltas": deltas,
        }

    monkeypatch.setattr(
        "bedc_quality_lab.torch_bedc_jepa._run_active_gap_ledger_curriculum_arm",
        fake_arm,
    )

    packet = run_active_gap_ledger_controlled(seeds=(1, 2), config=_small_config())

    assert packet["schema_id"] == "bedc-jepa-active-gap-ledger-controlled"
    assert set(packet["arms"]) == {"real", "coverage_preserving", "placebo"}
    assert len(packet["arms"]["real"]["runs"]) == 2
    assert packet["arms"]["coverage_preserving"]["summary"]["gap_detection_auc"]["mean"] == 0.72
    assert packet["decision"]["verdict"] == "real-capability-win"


def test_active_gap_ledger_cli_writes_fixed_report(monkeypatch):
    script = ROOT / "scripts" / "run_torch_active_gap_ledger.py"
    writes = {}
    monkeypatch.chdir(ROOT)
    monkeypatch.setattr(
        "bedc_quality_lab.torch_bedc_jepa.run_active_gap_ledger_curriculum",
        lambda: {
            "schema_id": "bedc-jepa-active-gap-ledger-curriculum",
            "status": "executed",
            "source": {},
            "thresholds": {},
            "sampling": {},
            "metrics_before": {},
            "metrics_after": {},
            "deltas": {},
            "guardrail": {},
            "minigrid_active_curriculum": {"status": "not_executed"},
            "cannot_claim": ["public MiniGrid active retraining"],
        },
    )
    original_write_text = Path.write_text

    def capture_write_text(self, data, *args, **kwargs):
        if self == ROOT / "reports" / "bedc_jepa_active_gap_ledger.json":
            writes["path"] = self
            writes["payload"] = data
            return len(data)
        return original_write_text(self, data, *args, **kwargs)

    monkeypatch.setattr(Path, "write_text", capture_write_text)
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))

    runpy.run_path(str(script), run_name="__main__")

    assert writes["path"].relative_to(ROOT).as_posix() == "reports/bedc_jepa_active_gap_ledger.json"
    payload = json.loads(writes["payload"])
    assert payload["schema_id"] == "bedc-jepa-active-gap-ledger-curriculum"
    assert payload["minigrid_active_curriculum"]["status"] == "not_executed"


def test_active_gap_ledger_controlled_cli_maps_args_writes_report_and_prints_summary(
    monkeypatch,
    capsys,
):
    script = ROOT / "scripts" / "run_active_gap_ledger_controlled.py"
    writes = {}
    calls = {}

    class Device:
        resolved_device = "cuda"

    packet = {
        "schema_id": "bedc-jepa-active-gap-ledger-controlled",
        "arms": {
            "real": {
                "summary": {
                    "gap_detection_auc": {"mean": 0.74},
                    "certified_coverage_delta": {"mean": 0.03},
                    "linear_identifiability_r2_delta": {"mean": 0.01},
                    "bedc_debt_score_delta": {"mean": -0.02},
                }
            },
            "coverage_preserving": {
                "summary": {
                    "gap_detection_auc": {"mean": 0.73},
                    "certified_coverage_delta": {"mean": 0.04},
                    "linear_identifiability_r2_delta": {"mean": 0.00},
                    "bedc_debt_score_delta": {"mean": -0.01},
                }
            },
            "placebo": {
                "summary": {
                    "gap_detection_auc": {"mean": 0.51},
                    "certified_coverage_delta": {"mean": 0.00},
                    "linear_identifiability_r2_delta": {"mean": -0.01},
                    "bedc_debt_score_delta": {"mean": 0.01},
                }
            },
        },
        "decision": {
            "verdict": "real-capability-win",
            "placebo_gap_detection_auc": 0.51,
            "placebo_certified_coverage_delta": 0.0,
            "placebo_linear_identifiability_r2_delta": -0.01,
            "qualifying_arms": ["real"],
        },
    }

    def fake_choose_device(requested_device="auto"):
        calls["requested_device"] = requested_device
        return Device()

    def fake_controlled(*, seeds, config, preserve_fraction):
        calls["seeds"] = seeds
        calls["config"] = config
        calls["preserve_fraction"] = preserve_fraction
        return packet

    original_write_text = Path.write_text

    def capture_write_text(self, data, *args, **kwargs):
        if self == ROOT / "reports" / "active_gap_ledger_controlled.json":
            writes["path"] = self
            writes["payload"] = data
            return len(data)
        return original_write_text(self, data, *args, **kwargs)

    monkeypatch.chdir(ROOT)
    monkeypatch.setattr("bedc_quality_lab.model.choose_device", fake_choose_device)
    monkeypatch.setattr(
        "bedc_quality_lab.torch_bedc_jepa.run_active_gap_ledger_controlled",
        fake_controlled,
    )
    monkeypatch.setattr(Path, "write_text", capture_write_text)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            str(script),
            "--seeds",
            "11,12",
            "--epochs",
            "7",
            "--initial-train-count",
            "90",
            "--pool-count",
            "210",
            "--test-count",
            "80",
            "--active-budget",
            "33",
            "--preserve-fraction",
            "0.25",
        ],
    )
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))

    runpy.run_path(str(script), run_name="__main__")

    assert calls["requested_device"] == "cuda"
    assert calls["seeds"] == (11, 12)
    assert calls["config"].initial_train_count == 90
    assert calls["config"].pool_count == 210
    assert calls["config"].test_count == 80
    assert calls["config"].active_budget == 33
    assert calls["config"].epochs == 7
    assert calls["config"].gap_auc_floor == 0.0
    assert calls["config"].gap_auc_min_delta == -1.0
    assert calls["config"].latent_r2_min_delta == -1.0
    assert calls["config"].unlogged_error_ceiling == 1.0
    assert calls["config"].coverage_min_delta == -1.0
    assert calls["preserve_fraction"] == 0.25
    assert writes["path"].relative_to(ROOT).as_posix() == "reports/active_gap_ledger_controlled.json"
    payload = json.loads(writes["payload"])
    assert payload["schema_id"] == "bedc-jepa-active-gap-ledger-controlled"
    assert payload["decision"]["verdict"] == "real-capability-win"
    output = capsys.readouterr().out
    assert "=== CONTROLLED RESULT ===" in output
    assert "arm gap_auc coverage_delta r2_delta debt_delta" in output
    assert "real 0.740000 0.030000 0.010000 -0.020000" in output
    assert "VERDICT real-capability-win:" in output


def test_active_gap_ledger_controlled_cli_rejects_non_cuda_device(monkeypatch):
    script = ROOT / "scripts" / "run_active_gap_ledger_controlled.py"
    calls = {"controlled": 0}

    class Device:
        resolved_device = "cpu"

    monkeypatch.chdir(ROOT)
    monkeypatch.setattr("bedc_quality_lab.model.choose_device", lambda requested_device="auto": Device())
    monkeypatch.setattr(
        "bedc_quality_lab.torch_bedc_jepa.run_active_gap_ledger_controlled",
        lambda **kwargs: calls.__setitem__("controlled", calls["controlled"] + 1),
    )
    monkeypatch.setattr(sys, "argv", [str(script)])
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))

    with pytest.raises(RuntimeError, match="requires cuda, got cpu"):
        runpy.run_path(str(script), run_name="__main__")

    assert calls["controlled"] == 0

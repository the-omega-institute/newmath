import json
import runpy
import sys
from pathlib import Path

import pytest

from bedc_quality_lab.torch_bedc_jepa import (
    ActiveGapLedgerConfig,
    _active_gap_guardrail,
    run_active_gap_ledger_curriculum,
)

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

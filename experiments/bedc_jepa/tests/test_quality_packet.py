import importlib.util

import pytest

from experiments.bedc_jepa.certs.build_ledger import build_ledger
from experiments.bedc_jepa.certs.build_namecert import build_namecert, render_namecert_yaml
from experiments.bedc_jepa.metrics.quality_gate import evaluate_quality_gate
from experiments.bedc_jepa.scripts.run_packet import build_packet


def test_quality_packet_records_trained_gap_ledger_objective():
    if importlib.util.find_spec("torch") is None:
        pytest.skip("torch is not installed")

    packet = build_packet()

    assert packet["schema_id"] == "bedc-jepa-quality-packet"
    assert packet["config"]["science_contract"]["progress_metric"] == "unlogged_error_rate"
    assert packet["quality_gate"]["decision"] == "pass"

    single = packet["benchmark"]["single"]
    latent = single["systems"]["latent_only"]
    bedc = single["systems"]["bedc_objective"]
    assert "unlogged_error_penalty" in single["objective_terms"]
    assert bedc["gap_detection_auc"] > latent["gap_detection_auc"]
    assert bedc["unlogged_error_rate"] <= latent["unlogged_error_rate"]
    assert packet["benchmark"]["sweep"]["unlogged_error_reduction_mean"] > 0.0


def test_quality_gate_fails_closed_on_missing_unlogged_reduction():
    packet = {
        "config": {
            "science_contract": {"progress_metric": "unlogged_error_rate"},
            "gate": {
                "max_bedc_unlogged_error_rate": 0.001,
                "min_unlogged_error_reduction_mean": 0.005,
                "min_gap_auc_gain_mean": 0.2,
                "min_debt_reduction_mean": 0.05,
                "max_latent_r2_delta_abs": 0.00000001,
            },
        },
        "benchmark": {
            "single": {
                "systems": {
                    "bedc_objective": {"unlogged_error_rate": 0.0},
                },
            },
            "sweep": {
                "unlogged_error_reduction_mean": 0.0,
                "gap_auc_gain_mean": 0.3,
                "debt_reduction_mean": 0.1,
                "latent_r2_delta_abs_max": 0.0,
            },
        },
    }

    gate = evaluate_quality_gate(packet)

    assert gate["decision"] == "fail"
    assert gate["blocking_checks"] == ["unlogged_error_reduction_mean"]


def test_namecert_and_ledger_are_packet_projections():
    packet = {
        "config": {
            "world": {"name": "boundary-gated-ou-world", "observation": "state", "test_count": 4},
            "model": {"bedc_objective": "torch-bedc-jepa-objective"},
            "distinctions": ["inside_operational_boundary"],
            "gap_types": ["boundary_gap"],
            "thresholds": {"distinction": 0.5, "gap": 0.5},
        },
        "benchmark": {
            "single": {
                "source": {"test_count": 4.0},
                "objective_terms": ["latent_prediction", "gap_bce"],
                "systems": {
                    "latent_only": {
                        "unlogged_error_rate": 0.25,
                    },
                    "bedc_objective": {
                        "distinction_accuracy": 1.0,
                        "distinction_accuracy_outside_gap": 1.0,
                        "unlogged_error_rate": 0.0,
                        "bedc_debt_score": 0.02,
                        "certified_coverage": 0.75,
                    },
                },
            },
            "sweep": {
                "seed_count": 3.0,
                "gap_auc_gain_mean": 0.4,
                "debt_reduction_mean": 0.1,
                "latent_r2_delta_abs_max": 0.0,
                "unlogged_error_reduction_mean": 0.2,
            },
        },
        "quality_gate": {"decision": "pass"},
    }

    namecert = build_namecert(packet)
    ledger = build_ledger(packet)
    yaml_text = render_namecert_yaml(namecert)

    assert namecert["quality"]["gate_decision"] == "pass"
    assert "BEDCJEPA_TinyWorld" in yaml_text
    assert ledger["residue"][1]["status"] == "closed"
    assert "open-domain semantic naming" in ledger["not_claimed"][1]

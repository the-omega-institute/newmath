"""Machine-readable contact readiness gate for BEDC-JEPA evidence."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


def _load_optional_json(name: str) -> dict[str, Any] | None:
    path = REPORTS / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _dependency_present(name: str) -> bool:
    return importlib.util.find_spec(name) is not None


def _gate(status: str, evidence: str, requirement: str) -> dict[str, str]:
    return {
        "status": status,
        "evidence": evidence,
        "requirement": requirement,
    }


def _torch_objective_gate(torch_objective: dict[str, Any] | None) -> dict[str, str]:
    if torch_objective is None or "sweep" not in torch_objective:
        return _gate("missing", "reports/bedc_jepa_torch_objective.json", "three-seed torch objective sweep")
    sweep = torch_objective["sweep"]
    passes = (
        float(sweep["gap_auc_gain_mean"]) > 0.20
        and float(sweep["debt_reduction_mean"]) > 0.05
        and float(sweep["latent_r2_delta_abs_max"]) < 1e-8
        and float(sweep["gap_auc_win_rate"]) >= 0.75
    )
    return _gate(
        "pass" if passes else "missing",
        "reports/bedc_jepa_torch_objective.json",
        "stable BEDC objective gain without latent R2 change",
    )


def _local_visual_gate(summary: dict[str, Any] | None) -> dict[str, str]:
    if summary is None:
        return _gate("missing", "reports/bedc_jepa_four_system_experiment.json", "local visual planning benchmark")
    planning = summary["minigrid_visual_planning"]["planning"]
    gain = float(planning["vanilla_minus_gap_aware_risk_adjusted_cost"])
    transition = float(summary["minigrid_visual_planning"]["transition"]["one_step_accuracy"])
    return _gate(
        "pass" if gain > 0.0 and transition > 0.94 else "missing",
        "reports/bedc_jepa_four_system_experiment.json",
        "local visual planning with learned transition and risk-adjusted gain",
    )


def _clutter_gate(summary: dict[str, Any] | None) -> dict[str, str]:
    if summary is None:
        return _gate("missing", "reports/bedc_jepa_four_system_experiment.json", "object counterfactual clutter sweep")
    clutter = summary["cluttered_object_sweep"]
    passes = (
        float(clutter["counterfactual_accuracy_mean"]) > 0.86
        and float(clutter["s3_minus_s2_gap_auc_mean"]) > 0.40
        and float(clutter["s2_minus_s3_unlogged_error_mean"]) > 0.20
    )
    return _gate(
        "pass" if passes else "missing",
        "reports/bedc_jepa_four_system_experiment.json",
        "object-level counterfactual readback under clutter",
    )


def _public_minigrid_gate(benchmark_packet: dict[str, Any] | None) -> dict[str, str]:
    if benchmark_packet is None:
        return _gate("missing", "reports/bedc_jepa_public_minigrid_benchmark_packet.json", "executed public MiniGrid benchmark")
    executed = benchmark_packet.get("status") == "available" and float(benchmark_packet["sample_count_collected"]) > 0.0
    deps = _dependency_present("gymnasium") and _dependency_present("minigrid")
    return _gate(
        "pass" if executed and deps else "missing",
        "reports/bedc_jepa_public_minigrid_benchmark_packet.json",
        "executed public MiniGrid DoorKey readback/gap benchmark",
    )


def _public_jepa_gate(comparison: dict[str, Any] | None) -> dict[str, str]:
    evidence = (
        "reports/bedc_jepa_public_baseline_comparison.json"
        if comparison is not None
        else "no public JEPA baseline comparison artifact recorded"
    )
    if comparison is not None and comparison.get("status") == "executed":
        return _gate(
            "pass",
            evidence,
            "public JEPA or JEPA-style baseline comparison",
        )
    return _gate(
        "missing",
        evidence,
        "public JEPA or JEPA-style baseline comparison",
    )


def build_bedc_jepa_readiness() -> dict[str, Any]:
    summary = _load_optional_json("bedc_jepa_four_system_experiment.json")
    torch_objective = _load_optional_json("bedc_jepa_torch_objective.json")
    public_minigrid = _load_optional_json("bedc_jepa_public_minigrid_benchmark_packet.json")
    public_jepa_comparison = _load_optional_json("bedc_jepa_public_baseline_comparison.json")
    gates = {
        "torch_objective_seed_sweep": _torch_objective_gate(torch_objective),
        "local_visual_planning": _local_visual_gate(summary),
        "object_counterfactual_clutter": _clutter_gate(summary),
        "public_minigrid_execution": _public_minigrid_gate(public_minigrid),
        "public_jepa_baseline": _public_jepa_gate(public_jepa_comparison),
    }
    blocking = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "schema_id": "bedc-jepa-readiness",
        "decision": "contact_ready" if not blocking else "not_contact_ready",
        "gates": gates,
        "blocking_gates": blocking,
        "next_actions": [
            "install gymnasium/minigrid or run on an environment where both are present",
            "execute the public MiniGrid DoorKey benchmark packet",
            "add a public JEPA or JEPA-style baseline artifact",
            "rerun the readiness gate before external contact",
        ],
    }


def write_bedc_jepa_readiness(path: str | Path) -> dict[str, Any]:
    readiness = build_bedc_jepa_readiness()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(readiness, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return readiness

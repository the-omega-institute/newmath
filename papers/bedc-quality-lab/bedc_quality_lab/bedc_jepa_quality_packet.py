"""Tiny-world BEDC-JEPA quality packet, gate, NameCert, and ledger projections."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from bedc_quality_lab.torch_bedc_jepa import run_torch_bedc_jepa_benchmark, run_torch_bedc_jepa_sweep


ROOT = Path(__file__).resolve().parents[1]


def build_bedc_jepa_quality_config() -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-target-profile",
        "slug": "bedc_jepa_tiny_world",
        "title": "BEDC-JEPA Tiny World: Certifiable Distinctions and Gap Ledger World Model",
        "profile_status": "ready",
        "science_contract": {
            "contribution_type": "construction",
            "target_lane": "frontier_lane",
            "terminal_artifact": "papers/bedc-quality-lab/reports/bedc_jepa_quality_packet.json",
            "verifier": "papers/bedc-quality-lab/scripts/check_bedc_jepa_quality_gate.py",
            "progress_metric": "unlogged_error_rate",
            "closure_status": "scoped_target",
            "verification_status": "artifact_present",
            "evidence_required": [
                "baseline metrics",
                "BEDC-JEPA metrics",
                "TensorNameCert YAML",
                "ledger JSON",
                "quality report",
            ],
            "taste_obligations": {
                "novelty_witness": (
                    "The training objective includes distinction and gap prediction, "
                    "not only post-hoc reporting."
                ),
                "no_hidden_assumption_witness": (
                    "The scope is a boundary-gated operational toy world with declared "
                    "predicates and gap labels."
                ),
                "reproducibility_witness": "Runs are config-driven with fixed seeds and generated evidence artifacts.",
                "layer_separation_witness": (
                    "Training results, certificate projections, paper claims, and Lean hardening remain separate."
                ),
            },
        },
        "world": {
            "name": "boundary-gated-ou-world",
            "observation": "nonlinear mixed state vector",
            "actions": "none",
            "train_count": 1536,
            "test_count": 768,
            "rho": 0.84,
            "radius": 1.0,
            "gap_width": 0.14,
        },
        "model": {
            "baseline": "torch-latent-only",
            "bedc_objective": "torch-bedc-jepa-objective",
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "gap_bce",
                "unlogged_error_penalty",
            ],
        },
        "distinctions": ["inside_operational_boundary"],
        "gap_types": [
            "boundary_gap",
            "low_certification_margin",
            "unlogged_distinction_error",
        ],
        "thresholds": {
            "distinction": 0.5,
            "gap": 0.5,
        },
        "gate": {
            "max_bedc_unlogged_error_rate": 0.001,
            "min_unlogged_error_reduction_mean": 0.005,
            "min_gap_auc_gain_mean": 0.2,
            "min_debt_reduction_mean": 0.05,
            "max_latent_r2_delta_abs": 0.00000001,
        },
    }


def evaluate_bedc_jepa_quality_gate(packet: dict[str, Any]) -> dict[str, Any]:
    config = packet["config"]
    gate = config["gate"]
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    bedc = single["systems"]["bedc_objective"]
    checks = {
        "bedc_unlogged_error_rate": {
            "value": float(bedc["unlogged_error_rate"]),
            "limit": float(gate["max_bedc_unlogged_error_rate"]),
            "status": (
                "pass"
                if float(bedc["unlogged_error_rate"]) <= float(gate["max_bedc_unlogged_error_rate"])
                else "fail"
            ),
        },
        "unlogged_error_reduction_mean": {
            "value": float(sweep["unlogged_error_reduction_mean"]),
            "limit": float(gate["min_unlogged_error_reduction_mean"]),
            "status": (
                "pass"
                if float(sweep["unlogged_error_reduction_mean"]) >= float(gate["min_unlogged_error_reduction_mean"])
                else "fail"
            ),
        },
        "gap_auc_gain_mean": {
            "value": float(sweep["gap_auc_gain_mean"]),
            "limit": float(gate["min_gap_auc_gain_mean"]),
            "status": "pass" if float(sweep["gap_auc_gain_mean"]) >= float(gate["min_gap_auc_gain_mean"]) else "fail",
        },
        "debt_reduction_mean": {
            "value": float(sweep["debt_reduction_mean"]),
            "limit": float(gate["min_debt_reduction_mean"]),
            "status": (
                "pass" if float(sweep["debt_reduction_mean"]) >= float(gate["min_debt_reduction_mean"]) else "fail"
            ),
        },
        "latent_r2_delta_abs": {
            "value": float(sweep["latent_r2_delta_abs_max"]),
            "limit": float(gate["max_latent_r2_delta_abs"]),
            "status": (
                "pass"
                if float(sweep["latent_r2_delta_abs_max"]) <= float(gate["max_latent_r2_delta_abs"])
                else "fail"
            ),
        },
    }
    blocking = [name for name, check in checks.items() if check["status"] != "pass"]
    return {
        "schema_id": "bedc-jepa-quality-gate",
        "decision": "pass" if not blocking else "fail",
        "blocking_checks": blocking,
        "progress_metric": config["science_contract"]["progress_metric"],
        "checks": checks,
    }


def _yaml_scalar(value: object) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    text = str(value)
    if text == "" or any(char in text for char in ":#[]{}&,*!|>'\"%@`"):
        return repr(text)
    return text


def _yaml_lines(value: object, indent: int = 0) -> list[str]:
    prefix = " " * indent
    if isinstance(value, dict):
        lines: list[str] = []
        for key, child in value.items():
            if isinstance(child, (dict, list)):
                lines.append(f"{prefix}{key}:")
                lines.extend(_yaml_lines(child, indent + 2))
            else:
                lines.append(f"{prefix}{key}: {_yaml_scalar(child)}")
        return lines
    if isinstance(value, list):
        lines = []
        for item in value:
            if isinstance(item, (dict, list)):
                lines.append(f"{prefix}-")
                lines.extend(_yaml_lines(item, indent + 2))
            else:
                lines.append(f"{prefix}- {_yaml_scalar(item)}")
        return lines
    return [f"{prefix}{_yaml_scalar(value)}"]


def build_bedc_jepa_namecert(packet: dict[str, Any]) -> dict[str, Any]:
    config = packet["config"]
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    bedc = single["systems"]["bedc_objective"]
    return {
        "schema_id": "bedc-jepa-tensor-namecert",
        "name": "BEDCJEPA_TinyWorld",
        "source_spec": {
            "world": config["world"]["name"],
            "model": config["model"]["bedc_objective"],
            "observation": config["world"]["observation"],
            "train_scope": "boundary-gated operational toy world",
            "test_count": single["source"]["test_count"],
        },
        "pattern_spec": {
            "distinctions": config["distinctions"],
            "gap_types": config["gap_types"],
            "objective_terms": single["objective_terms"],
        },
        "classifier_spec": {
            "relation": "same thresholded distinction vector inside declared low-gap scope",
            "distinction_threshold": config["thresholds"]["distinction"],
            "gap_threshold": config["thresholds"]["gap"],
            "distinction_accuracy": bedc["distinction_accuracy"],
            "distinction_accuracy_outside_gap": bedc["distinction_accuracy_outside_gap"],
        },
        "stab_cert": {
            "seed_count": sweep["seed_count"],
            "gap_auc_gain_mean": sweep["gap_auc_gain_mean"],
            "debt_reduction_mean": sweep["debt_reduction_mean"],
            "latent_r2_delta_abs_max": sweep["latent_r2_delta_abs_max"],
        },
        "ledger_policy": {
            "recorded_residue": [
                "gap-labeled boundary cases",
                "low-certification coverage cases",
                "distinction errors without active gap score",
            ],
            "not_claimed": [
                "real-world physics",
                "global planning optimality",
                "open-domain semantics",
                "formal verification of neural training",
            ],
        },
        "quality": {
            "unlogged_error_rate": bedc["unlogged_error_rate"],
            "unlogged_error_reduction_mean": sweep["unlogged_error_reduction_mean"],
            "bedc_debt_score": bedc["bedc_debt_score"],
            "gate_decision": packet["quality_gate"]["decision"],
        },
    }


def render_namecert_yaml(namecert: dict[str, Any]) -> str:
    return "\n".join(_yaml_lines(namecert)) + "\n"


def build_bedc_jepa_gap_ledger(packet: dict[str, Any]) -> dict[str, Any]:
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    latent = single["systems"]["latent_only"]
    bedc = single["systems"]["bedc_objective"]
    return {
        "schema_id": "bedc-jepa-gap-ledger",
        "scope": "boundary-gated operational toy world",
        "thresholds": packet["config"]["thresholds"],
        "residue": [
            {
                "kind": "unlogged_error",
                "system": "latent_only",
                "rate": latent["unlogged_error_rate"],
                "status": "open",
            },
            {
                "kind": "unlogged_error",
                "system": "bedc_objective",
                "rate": bedc["unlogged_error_rate"],
                "status": "closed" if float(bedc["unlogged_error_rate"]) <= 0.001 else "open",
            },
            {
                "kind": "coverage_tradeoff",
                "system": "bedc_objective",
                "certified_coverage": bedc["certified_coverage"],
                "status": "recorded",
            },
            {
                "kind": "latent_equivalence_boundary",
                "latent_r2_delta_abs_max": sweep["latent_r2_delta_abs_max"],
                "status": "recorded",
            },
        ],
        "not_claimed": [
            "The packet does not compare against an executed public JEPA implementation.",
            "The packet does not claim open-domain semantic naming.",
            "The packet does not verify SGD or neural-network convergence in Lean.",
        ],
    }


def build_bedc_jepa_quality_packet() -> dict[str, Any]:
    benchmark = {
        "single": run_torch_bedc_jepa_benchmark(),
        "sweep": run_torch_bedc_jepa_sweep(),
    }
    packet = {
        "schema_id": "bedc-jepa-quality-packet",
        "config": build_bedc_jepa_quality_config(),
        "benchmark": benchmark,
    }
    packet["quality_gate"] = evaluate_bedc_jepa_quality_gate(packet)
    packet["ledger"] = build_bedc_jepa_gap_ledger(packet)
    packet["namecert"] = build_bedc_jepa_namecert(packet)
    return packet


def render_bedc_jepa_quality_report(packet: dict[str, Any], namecert_path: str, ledger_path: str) -> str:
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    latent = single["systems"]["latent_only"]
    bedc = single["systems"]["bedc_objective"]
    gate = packet["quality_gate"]
    lines = [
        "# BEDC-JEPA Tiny World Quality Report",
        "",
        "## Scope",
        "",
        "- World: `boundary-gated-ou-world`",
        "- Baseline: `torch-latent-only`",
        "- BEDC objective: `torch-bedc-jepa-objective`",
        "- Primary metric: `unlogged_error_rate`",
        "",
        "## Objective",
        "",
        "- `latent_prediction`",
        "- `distinction_bce`",
        "- `gap_bce`",
        "- `unlogged_error_penalty`",
        "",
        "## Single Run",
        "",
        f"- Baseline unlogged error: `{float(latent['unlogged_error_rate']):.6f}`",
        f"- BEDC-JEPA unlogged error: `{float(bedc['unlogged_error_rate']):.6f}`",
        f"- Baseline gap AUROC: `{float(latent['gap_detection_auc']):.6f}`",
        f"- BEDC-JEPA gap AUROC: `{float(bedc['gap_detection_auc']):.6f}`",
        f"- Baseline debt: `{float(latent['bedc_debt_score']):.6f}`",
        f"- BEDC-JEPA debt: `{float(bedc['bedc_debt_score']):.6f}`",
        "",
        "## Seed Sweep",
        "",
        f"- Seed count: `{int(float(sweep['seed_count']))}`",
        f"- Mean unlogged-error reduction: `{float(sweep['unlogged_error_reduction_mean']):.6f}`",
        f"- Mean gap-AUROC gain: `{float(sweep['gap_auc_gain_mean']):.6f}`",
        f"- Mean debt reduction: `{float(sweep['debt_reduction_mean']):.6f}`",
        f"- Latent R2 delta absolute max: `{float(sweep['latent_r2_delta_abs_max']):.6g}`",
        "",
        "## Gate",
        "",
        f"- Decision: `{gate['decision']}`",
        f"- Blocking checks: `{', '.join(gate['blocking_checks']) if gate['blocking_checks'] else 'none'}`",
        "",
        "## Evidence",
        "",
        f"- NameCert: `{namecert_path}`",
        f"- Ledger: `{ledger_path}`",
        "- Quality packet: `papers/bedc-quality-lab/reports/bedc_jepa_quality_packet.json`",
        "",
        "## Not Claimed",
        "",
        "- Executed public JEPA implementation comparison.",
        "- Real-world physics.",
        "- Open-domain semantic naming.",
        "- Lean verification of neural training.",
    ]
    return "\n".join(lines) + "\n"


def write_bedc_jepa_quality_packet(report_dir: str | Path | None = None) -> dict[str, Any]:
    target_dir = Path(report_dir) if report_dir is not None else ROOT / "reports"
    target_dir.mkdir(parents=True, exist_ok=True)
    packet = build_bedc_jepa_quality_packet()
    packet_path = target_dir / "bedc_jepa_quality_packet.json"
    namecert_path = target_dir / "bedc_jepa_namecert.yaml"
    ledger_path = target_dir / "bedc_jepa_gap_ledger.json"
    report_path = target_dir / "bedc_jepa_quality_report.md"
    packet_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    namecert_path.write_text(render_namecert_yaml(packet["namecert"]), encoding="utf-8")
    ledger_path.write_text(json.dumps(packet["ledger"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(
        render_bedc_jepa_quality_report(
            packet,
            "papers/bedc-quality-lab/reports/bedc_jepa_namecert.yaml",
            "papers/bedc-quality-lab/reports/bedc_jepa_gap_ledger.json",
        ),
        encoding="utf-8",
    )
    return packet


def check_bedc_jepa_quality_packet(path: str | Path | None = None) -> dict[str, Any]:
    packet_path = Path(path) if path is not None else ROOT / "reports" / "bedc_jepa_quality_packet.json"
    if not packet_path.exists():
        raise FileNotFoundError(f"missing {packet_path}")
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    return evaluate_bedc_jepa_quality_gate(packet)

"""Build the BEDC-JEPA tiny world TensorNameCert projection."""

from __future__ import annotations

from typing import Any


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


def build_namecert(packet: dict[str, Any]) -> dict[str, Any]:
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


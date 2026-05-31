#!/usr/bin/env python3
"""Build the machine-readable BEDC-JEPA artifact manifest."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def _load_summary() -> dict[str, object]:
    path = ROOT / "reports" / "bedc_jepa_four_system_experiment.json"
    return json.loads(path.read_text(encoding="utf-8"))


def _load_optional_json(name: str) -> dict[str, object] | None:
    path = ROOT / "reports" / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _system_delta(section: dict[str, object], key: str) -> float:
    systems = section["systems"]
    return float(systems["S3"][key]) - float(systems["S2"][key])


def build_manifest(summary: dict[str, object]) -> dict[str, object]:
    grid = summary["grid_transition"]
    minigrid = summary["minigrid_visual_planning"]
    object_sweep = summary["object_intervention_sweep"]
    multi_sweep = summary["multi_object_distractor_sweep"]
    cluttered = summary["cluttered_object_sweep"]
    torch_objective = _load_optional_json("bedc_jepa_torch_objective.json")
    torch_claims = {}
    if torch_objective is not None:
        torch_single = torch_objective.get("single", torch_objective)
        torch_sweep = torch_objective.get("sweep")
        torch_claims = {
            "torch_objective_gap_auc_gain": torch_single["deltas"]["gap_auc_gain"],
            "torch_objective_debt_reduction": torch_single["deltas"]["debt_reduction"],
            "torch_objective_unlogged_error": torch_single["systems"]["bedc_objective"][
                "unlogged_error_rate"
            ],
            "torch_objective_latent_r2_delta": torch_single["deltas"]["latent_r2_delta"],
        }
        if torch_sweep is not None:
            torch_claims.update(
                {
                    "torch_objective_seed_count": torch_sweep["seed_count"],
                    "torch_objective_gap_auc_gain_mean": torch_sweep["gap_auc_gain_mean"],
                    "torch_objective_gap_auc_win_rate": torch_sweep["gap_auc_win_rate"],
                    "torch_objective_debt_reduction_mean": torch_sweep["debt_reduction_mean"],
                    "torch_objective_debt_win_rate": torch_sweep["debt_win_rate"],
                    "torch_objective_unlogged_error_reduction_mean": torch_sweep[
                        "unlogged_error_reduction_mean"
                    ],
                    "torch_objective_latent_r2_delta_abs_max": torch_sweep[
                        "latent_r2_delta_abs_max"
                    ],
                }
            )
    return {
        "schema_id": "bedc-jepa-artifact-manifest",
        "artifact": "reports/bedc_jepa_four_system_experiment.json",
        "commands": {
            "generate": "python scripts/run_bedc_jepa_experiment.py",
            "torch_objective": "python scripts/run_torch_bedc_jepa.py",
            "public_minigrid_probe": "python scripts/probe_public_minigrid.py",
            "test": "python -m pytest -q",
            "paper": "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        },
        "contact_ready_claims": {
            "four_system_ablation": sorted(summary["systems"].keys()),
            "grid_transition_one_step_r2": grid["transition"]["one_step_r2"],
            "minigrid_transition_one_step_accuracy": minigrid["transition"]["one_step_accuracy"],
            "minigrid_gap_auc_gain": _system_delta(minigrid, "gap_detection_auc"),
            "minigrid_risk_adjusted_planning_gain": minigrid["planning"][
                "vanilla_minus_gap_aware_risk_adjusted_cost"
            ],
            "object_intervention_counterfactual_accuracy_mean": object_sweep[
                "counterfactual_accuracy_mean"
            ],
            "multi_object_counterfactual_accuracy_mean": multi_sweep[
                "counterfactual_accuracy_mean"
            ],
            "cluttered_object_counterfactual_accuracy_mean": cluttered[
                "counterfactual_accuracy_mean"
            ],
            "cluttered_object_gap_auc_gain_mean": cluttered[
                "s3_minus_s2_gap_auc_mean"
            ],
            "cluttered_object_unlogged_error_reduction_mean": cluttered[
                "s2_minus_s3_unlogged_error_mean"
            ],
            **torch_claims,
        },
        "objective_artifacts": {
            "torch": "reports/bedc_jepa_torch_objective.json",
        },
        "public_adapters": {
            "minigrid": "reports/bedc_jepa_public_minigrid_probe.json",
            "minigrid_transition_packet": "reports/bedc_jepa_public_minigrid_transition_packet.json",
        },
        "cannot_claim": [
            "public JEPA implementation comparison",
            "robotics benchmark result",
            "natural-video object interaction",
            "general autonomous intelligence",
        ],
    }


def write_manifest() -> Path:
    manifest = build_manifest(_load_summary())
    path = ROOT / "reports" / "bedc_jepa_artifact_manifest.json"
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def main() -> None:
    path = write_manifest()
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

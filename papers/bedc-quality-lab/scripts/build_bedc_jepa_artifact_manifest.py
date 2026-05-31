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


def _system_delta(section: dict[str, object], key: str) -> float:
    systems = section["systems"]
    return float(systems["S3"][key]) - float(systems["S2"][key])


def build_manifest(summary: dict[str, object]) -> dict[str, object]:
    grid = summary["grid_transition"]
    minigrid = summary["minigrid_visual_planning"]
    object_sweep = summary["object_intervention_sweep"]
    multi_sweep = summary["multi_object_distractor_sweep"]
    cluttered = summary["cluttered_object_sweep"]
    return {
        "schema_id": "bedc-jepa-artifact-manifest",
        "artifact": "reports/bedc_jepa_four_system_experiment.json",
        "commands": {
            "generate": "python scripts/run_bedc_jepa_experiment.py",
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

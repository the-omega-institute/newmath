"""External execution contract for closing BEDC-JEPA readiness gates."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def build_external_run_kit() -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-external-run-kit",
        "status": "contract_only",
        "required_external_results": {
            "public_minigrid_execution": {
                "readiness_gate": "public_minigrid_execution",
                "target_artifact": "reports/bedc_jepa_public_minigrid_benchmark_packet.json",
                "export_command": "python scripts/export_public_minigrid_benchmark_result.py",
                "import_command": "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>",
                "required_fields": [
                    "environment_id",
                    "seed",
                    "sample_count_requested",
                    "sample_count_collected",
                    "distinction_accuracy",
                    "gap_detection_auc",
                    "unlogged_error_rate",
                    "certified_coverage",
                    "bedc_debt_score",
                ],
                "pass_condition": "target artifact status is available and sample_count_collected is positive",
            },
            "public_jepa_baseline": {
                "readiness_gate": "public_jepa_baseline",
                "target_artifact": "reports/bedc_jepa_public_baseline_comparison.json",
                "probe_command": "python scripts/probe_public_jepa_baseline.py",
                "export_command": "python scripts/export_public_jepa_baseline_result.py",
                "import_command": "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
                "required_fields": [
                    "candidate_id",
                    "commit",
                    "checkpoint",
                    "reported_benchmark_name",
                    "latent_prediction_score",
                    "rollout_or_planning_score",
                ],
                "pass_condition": "target artifact status is executed",
            },
        },
        "readiness_command": "python scripts/build_bedc_jepa_readiness.py",
        "verification_commands": [
            "python -m pytest -q",
            "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        ],
        "cannot_claim_until_ready": [
            "public JEPA implementation comparison",
            "public MiniGrid execution",
            "contact-ready external bundle",
        ],
    }


def write_external_run_kit(path: str | Path) -> dict[str, Any]:
    kit = build_external_run_kit()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(kit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return kit

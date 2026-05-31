"""Public JEPA-family baseline registry for BEDC-JEPA contact readiness."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def _vjepa2_ac_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "vjepa2-ac",
        "name": "V-JEPA 2-AC",
        "repository_url": "https://github.com/facebookresearch/vjepa2",
        "baseline_role": "action-conditioned latent world-model baseline",
        "why_relevant": (
            "V-JEPA 2-AC is the closest public JEPA-family contact because it "
            "uses action-conditioned latent prediction for world modeling."
        ),
        "expected_input_contract": [
            "visual observations or video frames",
            "action sequence or action token stream",
        ],
        "expected_output_contract": [
            "latent rollout or predicted representation",
            "planning or control-facing latent state",
        ],
        "bedc_comparison_contract": [
            "same observation/action stream",
            "matched latent readback scope where feasible",
            "BEDC distinction head and gap head evaluated on the same rollout cases",
            "unlogged error, gap AUROC, certified coverage, and debt reported beside baseline scores",
        ],
        "current_artifact_status": "not_executed",
    }


def _leworldmodel_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "leworldmodel-lejepa",
        "name": "LeWorldModel / LeJEPA baseline",
        "repository_url": "https://github.com/lucas-maes/le-wm",
        "baseline_role": "LeJEPA-style pixel world-model baseline",
        "why_relevant": (
            "LeWorldModel reports stable end-to-end JEPA world modeling from "
            "pixels and publishes LeJEPA baseline checkpoints and data pointers."
        ),
        "expected_input_contract": [
            "pixel observations",
            "benchmark configuration and checkpoint/data path",
        ],
        "expected_output_contract": [
            "next-embedding prediction score",
            "planning or rollout quality metrics where available",
        ],
        "bedc_comparison_contract": [
            "same pixel benchmark split",
            "baseline next-embedding prediction metrics",
            "BEDC objective readback metrics on the declared distinction/gap scope",
        ],
        "current_artifact_status": "not_executed",
    }


def build_public_jepa_baseline_registry() -> dict[str, Any]:
    candidates = [_vjepa2_ac_candidate(), _leworldmodel_candidate()]
    return {
        "schema_id": "bedc-jepa-public-baseline-registry",
        "status": "contract_only",
        "selected_candidate_id": "vjepa2-ac",
        "candidates": candidates,
        "execution_status": {
            "status": "missing",
            "reason": "no public JEPA-family baseline has been cloned, vendored, or executed in this workspace",
        },
        "next_actions": [
            "clone or vendor the selected public baseline in an approved environment",
            "record the exact commit, checkpoint, dataset, and command line",
            "run the selected baseline on a public visual/action benchmark",
            "export baseline metrics into a BEDC-JEPA comparison artifact",
        ],
    }


def write_public_jepa_baseline_registry(path: str | Path) -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return registry

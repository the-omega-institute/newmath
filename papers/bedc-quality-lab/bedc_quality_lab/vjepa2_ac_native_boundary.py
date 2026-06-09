"""Fail-closed boundary for native V-JEPA2-AC public benchmark reproduction."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def build_vjepa2_ac_native_boundary() -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-vjepa2-ac-native-boundary",
        "status": "not_executed",
        "candidate_id": "vjepa2-ac-vit-giant",
        "repository_url": "https://github.com/facebookresearch/vjepa2",
        "checkpoint_url": "https://dl.fbaipublicfiles.com/vjepa2/vjepa2-ac-vitg.pt",
        "target_public_benchmark": "MiniGrid-DoorKey-8x8-v0",
        "native_reproduction_status": "not_evaluated",
        "fixed_checkpoint_latent_prediction_status": "executed",
        "required_native_contract": [
            "same public image/action stream as the native MiniGrid BEDC-JEPA packet",
            "official V-JEPA2-AC benchmark reproduction or rollout benchmark score",
            "checkpoint commit and command line",
            "BEDC readback metrics reported beside native score",
        ],
        "current_contact_artifacts": [
            "reports/bedc_jepa_public_ac_giant_adapter.json",
            "reports/bedc_jepa_public_cuda_adapter_comparison.json",
            "reports/bedc_jepa_public_native_minigrid_benchmark.json",
            "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
        ],
        "blocking_boundary": (
            "The current AC Giant evidence is a checkpoint-scope evaluation on a declared tiny-world adapter protocol. "
            "The current native public MiniGrid evidence is a BEDC-JEPA S0/S1/S2/S3 packet with a JEPA-style S0 control row. "
            "A fixed-checkpoint V-JEPA2-AC MiniGrid latent-prediction contact artifact is evaluated. "
            "The remaining unevaluated scope is official V-JEPA2-AC benchmark reproduction or rollout benchmark parity."
        ),
        "cannot_claim": [
            "native V-JEPA2-AC benchmark reproduction",
            "public benchmark superiority",
            "checkpoint native evaluation parity",
        ],
    }


def write_vjepa2_ac_native_boundary(path: str | Path) -> dict[str, Any]:
    packet = build_vjepa2_ac_native_boundary()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

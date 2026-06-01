"""Build the BEDC-JEPA tiny world ledger projection."""

from __future__ import annotations

from typing import Any


def build_ledger(packet: dict[str, Any]) -> dict[str, Any]:
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


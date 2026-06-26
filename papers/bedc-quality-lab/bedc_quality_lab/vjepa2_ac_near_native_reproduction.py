"""Near-native V-JEPA2-AC MiniGrid record composed from fixed-checkpoint reports."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"
VJEPA2_REPOSITORY_URL = "https://github.com/facebookresearch/vjepa2"
VJEPA2_REPOSITORY_HEAD = "204698b45b3712590f06245fbfba32d3be539812"


def _load_json(name: str) -> dict[str, Any]:
    path = REPORTS / name
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"report must be a JSON object: {name}")
    return payload


def _status_counts(claims: list[Mapping[str, Any]]) -> dict[str, float]:
    counts: dict[str, float] = {}
    for claim in claims:
        status = str(claim.get("claim_status") or "unknown")
        counts[status] = counts.get(status, 0.0) + 1.0
    return counts


def _primary_means(claims: list[Mapping[str, Any]]) -> dict[str, float]:
    primaries = [claim.get("primary") for claim in claims if isinstance(claim.get("primary"), Mapping)]
    if not primaries:
        return {
            "mean_certified_coverage": 0.0,
            "mean_unlogged_error": 0.0,
            "mean_conformal_miscoverage": 0.0,
            "mean_outside_gap_accuracy": 0.0,
        }
    return {
        "mean_certified_coverage": sum(float(row.get("certified_coverage", 0.0)) for row in primaries)
        / len(primaries),
        "mean_unlogged_error": sum(float(row.get("unlogged_error", 0.0)) for row in primaries)
        / len(primaries),
        "mean_conformal_miscoverage": sum(float(row.get("conformal_miscoverage", 0.0)) for row in primaries)
        / len(primaries),
        "mean_outside_gap_accuracy": sum(float(row.get("outside_gap_accuracy", 0.0)) for row in primaries)
        / len(primaries),
    }


def _bedc_readback_metrics(certificate: Mapping[str, Any]) -> dict[str, Any]:
    claims = certificate.get("claims", [])
    if not isinstance(claims, list):
        claims = []
    typed_claims = [claim for claim in claims if isinstance(claim, Mapping)]
    return {
        "accepted_claim_count": float(certificate.get("accepted_claim_count", 0.0)),
        "gap_claim_count": float(certificate.get("gap_claim_count", 0.0)),
        "claim_status_counts": _status_counts(typed_claims),
        "predicate_count": float(len(typed_claims)),
        "predicates": [str(claim.get("predicate") or "") for claim in typed_claims],
        **_primary_means(typed_claims),
    }


def build_vjepa2_ac_near_native_reproduction(
    *,
    latent_prediction: Mapping[str, Any] | None = None,
    certificate: Mapping[str, Any] | None = None,
    native_minigrid: Mapping[str, Any] | None = None,
    native_boundary: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    latent = dict(latent_prediction or _load_json("bedc_vjepa2_ac_minigrid_latent_prediction.json"))
    lccp = dict(certificate or _load_json("bedc_vjepa2_ac_minigrid_claim_certificate.json"))
    native = dict(native_minigrid or _load_json("bedc_jepa_public_native_minigrid_benchmark.json"))
    boundary = dict(native_boundary or _load_json("bedc_jepa_vjepa2_ac_native_boundary.json"))

    metrics = latent.get("metrics", {})
    checkpoint = latent.get("checkpoint_contract", {})
    latent_execution = latent.get("execution_contract", {})
    lccp_execution = lccp.get("execution_contract", {})
    readback_metrics = _bedc_readback_metrics(lccp)
    latent_score = float(metrics.get("latent_prediction_score", 0.0))
    parity_gaps = [
        "official V-JEPA2-AC benchmark protocol is not evaluated",
        "the latent-prediction split and LCCP calibration split are both declared but are not a single official benchmark split",
        "the record reports fixed-checkpoint MiniGrid readback rather than an official V-JEPA2-AC rollout benchmark score",
    ]
    packet = {
        "schema_id": "bedc-vjepa2-ac-near-native-minigrid-reproduction",
        "status": "evaluated_near_native",
        "official_native_reproduction_status": "not_evaluated",
        "near_native_protocol_status": "executed",
        "candidate_id": str(latent.get("candidate_id") or "vjepa2-ac-vit-giant"),
        "carrier_id": str(latent.get("carrier_id") or lccp.get("carrier_id") or ""),
        "public_environment_id": str(latent.get("environment_id") or native.get("environment_id") or ""),
        "image_action_stream_split": {
            "latent_prediction": latent_execution,
            "lccp_certificate": lccp_execution,
            "native_minigrid_bedc_packet": {
                "train_count": float(native.get("train_count", 0.0)),
                "test_count": float(native.get("test_count", 0.0)),
                "sample_count_collected": float(native.get("sample_count_collected", 0.0)),
                "planning_state_count_collected": float(native.get("planning_state_count_collected", 0.0)),
            },
        },
        "vjepa2_repository_commit": VJEPA2_REPOSITORY_HEAD,
        "repository_identity": {
            "repository_url": VJEPA2_REPOSITORY_URL,
            "repository_commit": VJEPA2_REPOSITORY_HEAD,
            "identity_command": "git ls-remote https://github.com/facebookresearch/vjepa2 HEAD",
            "identity_scope": (
                "public repository identity for the torch hub source target used by the fixed-checkpoint "
                "MiniGrid record; this does not assert official V-JEPA2-AC benchmark reproduction"
            ),
        },
        "checkpoint_identity": {
            "repository_url": checkpoint.get("repository_url"),
            "hub_entry": checkpoint.get("hub_entry"),
            "checkpoint_url": checkpoint.get("checkpoint_url"),
            "candidate_id": checkpoint.get("candidate_id"),
            "loaded_components": checkpoint.get("loaded_components", []),
        },
        "execution_command": [
            "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
            "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
            "python scripts/build_vjepa2_ac_near_native_reproduction.py",
        ],
        "native_or_near_native_rollout_score": {
            "score_name": "fixed_checkpoint_latent_prediction_score",
            "value": latent_score,
            "official_rollout_score_status": "not_evaluated",
        },
        "latent_prediction_score": latent_score,
        "latent_prediction_metrics": metrics,
        "bedc_readback_metrics": readback_metrics,
        "lccp_certificate_metrics": {
            "status": lccp.get("status"),
            "risk_level": float(lccp.get("risk_level", 0.0)),
            "alphas": lccp.get("alphas", []),
            "accepted_claim_count": readback_metrics["accepted_claim_count"],
            "gap_claim_count": readback_metrics["gap_claim_count"],
            "claim_status_counts": readback_metrics["claim_status_counts"],
        },
        "parity_protocol": {
            "same_observation_preprocessing": "declared by MiniGrid two-frame 256x256 RGB video contracts",
            "same_action_encoding": "declared by one-hot MiniGrid action contracts",
            "same_train_cal_test_split": "declared separately for latent prediction and LCCP; not an official benchmark split",
            "same_planning_or_rollout_target": "fixed-checkpoint latent prediction and readback only; official rollout target not evaluated",
            "same_bedc_predicate_set": "LCCP predicate set is recorded beside the fixed carrier",
            "same_alpha_grid": "recorded in the LCCP certificate",
        },
        "parity_gaps": parity_gaps,
        "source_boundary": boundary.get("remaining_boundary", ""),
        "claim_status": "near_native_fixed_checkpoint_record_with_official_reproduction_gap",
        "cannot_claim_boundary": [
            "official V-JEPA2-AC benchmark reproduction",
            "public benchmark superiority",
            "checkpoint native evaluation parity",
            "end-to-end V-JEPA2-AC retraining",
            "certified natural-language semantic grounding",
        ],
    }
    return packet


def build_vjepa2_ac_native_readback_comparison(
    *,
    near_native: Mapping[str, Any] | None = None,
    native_minigrid: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    packet = dict(near_native or build_vjepa2_ac_near_native_reproduction())
    native = dict(native_minigrid or _load_json("bedc_jepa_public_native_minigrid_benchmark.json"))
    systems = native.get("systems", {})
    s0 = systems.get("S0", {}) if isinstance(systems, Mapping) else {}
    s3 = systems.get("S3", {}) if isinstance(systems, Mapping) else {}
    return {
        "schema_id": "bedc-vjepa2-ac-native-readback-comparison",
        "status": "evaluated_near_native",
        "official_native_reproduction_status": packet["official_native_reproduction_status"],
        "candidate_id": packet["candidate_id"],
        "public_environment_id": packet["public_environment_id"],
        "comparison_scope": (
            "fixed-checkpoint V-JEPA2-AC MiniGrid latent prediction and LCCP readback are placed beside "
            "the BEDC-JEPA public MiniGrid S0/S3 rows; this is not a superiority comparison"
        ),
        "vjepa2_ac_fixed_checkpoint": {
            "latent_prediction_score": packet["latent_prediction_score"],
            "bedc_readback_metrics": packet["bedc_readback_metrics"],
            "lccp_certificate_metrics": packet["lccp_certificate_metrics"],
            "claim_status": packet["claim_status"],
        },
        "bedc_jepa_public_minigrid": {
            "s0_unlogged_error": float(s0.get("unlogged_error_rate", 0.0)),
            "s3_unlogged_error": float(s3.get("unlogged_error_rate", 0.0)),
            "s0_gap_auc": float(s0.get("gap_detection_auc", 0.0)),
            "s3_gap_auc": float(s3.get("gap_detection_auc", 0.0)),
            "s0_debt": float(s0.get("bedc_debt_score", 0.0)),
            "s3_debt": float(s3.get("bedc_debt_score", 0.0)),
        },
        "claim_rule": (
            "The comparison may report co-located readback metrics, but it does not assert that BEDC-JEPA "
            "outperforms V-JEPA2-AC on an official or native V-JEPA2-AC benchmark."
        ),
        "cannot_claim_boundary": packet["cannot_claim_boundary"],
    }


def write_vjepa2_ac_near_native_reproduction(
    reproduction_path: str | Path,
    comparison_path: str | Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    reproduction = build_vjepa2_ac_near_native_reproduction()
    comparison = build_vjepa2_ac_native_readback_comparison(near_native=reproduction)
    target_reproduction = Path(reproduction_path)
    target_comparison = Path(comparison_path)
    target_reproduction.parent.mkdir(parents=True, exist_ok=True)
    target_comparison.parent.mkdir(parents=True, exist_ok=True)
    target_reproduction.write_text(json.dumps(reproduction, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    target_comparison.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return reproduction, comparison

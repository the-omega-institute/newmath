"""Canonical report reproducibility contract validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from bedc_quality_lab.canonical_digest import canonical_json_digest


REPRODUCIBILITY_CONTRACT_SCHEMA_ID = "bedc-quality-lab:canonical-reproducibility-contract"
REPRODUCIBILITY_MODES = frozenset({"exact_fixture", "true_training"})
REQUESTED_DEVICES = frozenset({"auto", "cpu", "mps", "cuda"})
RESOLVED_DEVICES = frozenset({"cpu", "mps", "cuda", "not-requested", "not-available"})
RESOLUTION_STATUSES = frozenset({"available", "fallback", "unavailable", "not-requested"})


@dataclass(frozen=True)
class CanonicalReproducibilityContract:
    mode: str
    seed_list: tuple[int, ...]
    metric_bands: tuple[dict[str, Any], ...]
    device_policy: dict[str, Any]
    framework_provenance: dict[str, Any]
    calibration: dict[str, Any]

    def to_payload(self) -> dict[str, Any]:
        return {
            "schema_id": REPRODUCIBILITY_CONTRACT_SCHEMA_ID,
            "mode": self.mode,
            "seed_list": list(self.seed_list),
            "metric_bands": list(self.metric_bands),
            "device_policy": self.device_policy,
            "framework_provenance": self.framework_provenance,
            "calibration": self.calibration,
        }

    def digest(self) -> str:
        return canonical_json_digest(self.to_payload())


def _require_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def validate_device_policy(policy: Mapping[str, Any], *, mode: str) -> dict[str, Any]:
    if mode not in REPRODUCIBILITY_MODES:
        raise ValueError(f"unsupported reproducibility mode: {mode}")
    recorded = dict(_require_mapping(policy, "device_policy"))
    for key in ("requested_device", "resolved_device", "resolution_status", "resolution_reason", "backend_details"):
        if key not in recorded:
            raise ValueError(f"device_policy missing {key}")
    requested = recorded["requested_device"]
    resolved = recorded["resolved_device"]
    status = recorded["resolution_status"]
    reason = recorded["resolution_reason"]
    backend_details = recorded["backend_details"]
    if requested not in REQUESTED_DEVICES:
        raise ValueError(f"invalid requested_device: {requested}")
    if resolved not in RESOLVED_DEVICES:
        raise ValueError(f"invalid resolved_device: {resolved}")
    if status not in RESOLUTION_STATUSES:
        raise ValueError(f"invalid resolution_status: {status}")
    if not isinstance(reason, str) or not reason:
        raise ValueError("device_policy resolution_reason must be a non-empty string")
    if not isinstance(backend_details, Mapping):
        raise ValueError("device_policy backend_details must be an object")
    if mode == "exact_fixture" and (requested != "cpu" or resolved != "cpu"):
        raise ValueError("exact_fixture device_policy must request and resolve cpu")
    return {
        "requested_device": requested,
        "resolved_device": resolved,
        "resolution_status": status,
        "resolution_reason": reason,
        "backend_details": dict(backend_details),
    }


def _validate_seed_list(value: Any) -> tuple[int, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise ValueError("seed_list must be a non-empty array")
    seeds = tuple(int(seed) for seed in value)
    if not seeds:
        raise ValueError("seed_list must be non-empty")
    return seeds


def _validate_metric_band(band: Any) -> dict[str, Any]:
    recorded = dict(_require_mapping(band, "metric band"))
    for key in ("pointer", "reference_value", "tolerance", "comparison", "owner", "calibration_source", "seed_basis"):
        if key not in recorded:
            raise ValueError(f"metric band missing {key}")
    if not isinstance(recorded["pointer"], str) or not recorded["pointer"]:
        raise ValueError("metric band pointer must be a non-empty string")
    if not isinstance(recorded["owner"], str) or not recorded["owner"]:
        raise ValueError("metric band owner must be a non-empty string")
    if not isinstance(recorded["calibration_source"], str) or not recorded["calibration_source"]:
        raise ValueError("metric band calibration_source must be a non-empty string")
    if recorded["comparison"] not in {"absolute", "lower_bound", "upper_bound", "status_equal"}:
        raise ValueError(f"unsupported metric band comparison: {recorded['comparison']}")
    if recorded["comparison"] == "status_equal":
        if not isinstance(recorded["reference_value"], str):
            raise ValueError("status_equal reference_value must be a string")
        if recorded["tolerance"] != 0:
            raise ValueError("status_equal tolerance must be zero")
    else:
        float(recorded["reference_value"])
        tolerance = float(recorded["tolerance"])
        if tolerance < 0:
            raise ValueError("metric band tolerance must be non-negative")
        recorded["reference_value"] = float(recorded["reference_value"])
        recorded["tolerance"] = tolerance
    seed_basis = _require_mapping(recorded["seed_basis"], "metric band seed_basis")
    if int(seed_basis.get("seed_count", 0)) <= 0:
        raise ValueError("metric band seed_basis.seed_count must be positive")
    recorded["seed_basis"] = dict(seed_basis)
    return recorded


def _validate_metric_bands(value: Any) -> tuple[dict[str, Any], ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise ValueError("metric_bands must be a non-empty array")
    bands = tuple(_validate_metric_band(band) for band in value)
    if not bands:
        raise ValueError("metric_bands must be non-empty")
    return bands


def _validate_framework_provenance(value: Any) -> dict[str, Any]:
    recorded = dict(_require_mapping(value, "framework_provenance"))
    for key in ("python", "dependency_abi"):
        if key not in recorded:
            raise ValueError(f"framework_provenance missing {key}")
    _require_mapping(recorded["dependency_abi"], "framework_provenance.dependency_abi")
    return recorded


def _validate_calibration(value: Any) -> dict[str, Any]:
    recorded = dict(_require_mapping(value, "calibration"))
    for key in ("calibration_source", "owner", "basis"):
        if key not in recorded:
            raise ValueError(f"calibration missing {key}")
    if not isinstance(recorded["calibration_source"], str) or not recorded["calibration_source"]:
        raise ValueError("calibration_source must be a non-empty string")
    return recorded


def validate_metric_values(contract: CanonicalReproducibilityContract, payload: Mapping[str, Any]) -> None:
    for band in contract.metric_bands:
        value = _resolve_pointer(payload, str(band["pointer"]))
        comparison = band["comparison"]
        if comparison == "status_equal":
            if value != band["reference_value"]:
                raise ValueError(f"metric outside tolerance at {band['pointer']}")
            continue
        numeric = float(value)
        reference = float(band["reference_value"])
        tolerance = float(band["tolerance"])
        if comparison == "absolute" and abs(numeric - reference) > tolerance:
            raise ValueError(f"metric outside tolerance at {band['pointer']}")
        if comparison == "lower_bound" and numeric + tolerance < reference:
            raise ValueError(f"metric below tolerance band at {band['pointer']}")
        if comparison == "upper_bound" and numeric - tolerance > reference:
            raise ValueError(f"metric above tolerance band at {band['pointer']}")


def _resolve_pointer(payload: Mapping[str, Any], pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        raise ValueError(f"unsupported pointer: {pointer}")
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if not isinstance(cursor, Mapping) or part not in cursor:
            raise ValueError(f"missing pointer value: {pointer}")
        cursor = cursor[part]
    return cursor


def contract_from_payload(payload: Mapping[str, Any]) -> CanonicalReproducibilityContract:
    recorded = dict(_require_mapping(payload.get("reproducibility_contract"), "reproducibility_contract"))
    mode = recorded.get("mode")
    if mode not in REPRODUCIBILITY_MODES:
        raise ValueError(f"unsupported reproducibility mode: {mode}")
    contract = CanonicalReproducibilityContract(
        mode=str(mode),
        seed_list=_validate_seed_list(recorded.get("seed_list")),
        metric_bands=_validate_metric_bands(recorded.get("metric_bands")),
        device_policy=validate_device_policy(_require_mapping(recorded.get("device_policy"), "device_policy"), mode=str(mode)),
        framework_provenance=_validate_framework_provenance(recorded.get("framework_provenance")),
        calibration=_validate_calibration(recorded.get("calibration")),
    )
    if contract.mode == "true_training":
        validate_metric_values(contract, payload)
    return contract

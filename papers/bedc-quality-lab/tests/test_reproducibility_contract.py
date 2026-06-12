import copy

import pytest

from bedc_quality_lab import reproducibility
from bedc_quality_lab.reproducibility import contract_from_payload


def _device_policy(requested="auto", resolved="cpu"):
    return {
        "requested_device": requested,
        "resolved_device": resolved,
        "resolution_status": "fallback" if requested == "auto" and resolved == "cpu" else "available",
        "resolution_reason": "fixture-policy",
        "backend_details": {"torch": "fixture"},
    }


def _payload(*, mode="true_training", device_policy=None):
    return {
        "metric": {"value": 0.25},
        "reproducibility_contract": {
            "mode": mode,
            "seed_list": [1, 2, 3],
            "metric_bands": [
                {
                    "pointer": "$.metric.value",
                    "reference_value": 0.25,
                    "tolerance": 0.001,
                    "comparison": "absolute",
                    "owner": "fixture-owner",
                    "calibration_source": "$.metric",
                    "seed_basis": {"seed_count": 3, "source": "$.seed_list"},
                }
            ],
            "device_policy": device_policy or _device_policy(),
            "framework_provenance": {
                "python": "fixture",
                "dependency_abi": {"torch": "fixture"},
            },
            "calibration": {
                "calibration_source": "$.metric",
                "owner": "fixture-owner",
                "basis": "seed variance fixture",
            },
        },
    }


def test_contract_digest_changes_when_device_policy_changes():
    cpu = contract_from_payload(_payload(device_policy=_device_policy("auto", "cpu")))
    mps = contract_from_payload(_payload(device_policy=_device_policy("mps", "mps")))

    assert cpu.digest() != mps.digest()


def test_exact_fixture_rejects_non_cpu_policy():
    payload = _payload(mode="exact_fixture", device_policy=_device_policy("auto", "mps"))

    with pytest.raises(ValueError, match="exact_fixture device_policy"):
        contract_from_payload(payload)


def test_true_training_rejects_missing_device_policy_fields():
    payload = _payload()
    del payload["reproducibility_contract"]["device_policy"]["resolution_reason"]

    with pytest.raises(ValueError, match="resolution_reason"):
        contract_from_payload(payload)


def test_true_training_rejects_metric_outside_tolerance():
    payload = _payload()
    payload["metric"]["value"] = 0.5

    with pytest.raises(ValueError, match="outside tolerance"):
        contract_from_payload(payload)


def test_reproducibility_module_has_no_device_resolver():
    assert not hasattr(reproducibility, "resolve_canonical_device")
    assert not hasattr(reproducibility, "choose_device")

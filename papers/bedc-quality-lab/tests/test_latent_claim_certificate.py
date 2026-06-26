import numpy as np

from bedc_quality_lab.latent_claim_certificate import (
    ALPHAS,
    PRIMARY_ALPHA,
    LatentCarrierSplit,
    build_latent_claim_certificate_artifacts,
    certify_latent_claim,
    source_gap_claim,
)


def _synthetic_split(seed: int = 20260607) -> LatentCarrierSplit:
    rng = np.random.default_rng(seed)
    z = rng.normal(size=(384, 2))
    features = np.column_stack(
        [
            z[:, 0],
            z[:, 1],
            np.sin(z[:, 0]),
            np.sin(z[:, 1]),
            z[:, 0] * z[:, 1],
        ]
    )
    labels = np.sum(z * z, axis=1) <= 1.0
    return LatentCarrierSplit(
        carrier_id="synthetic-frozen-carrier",
        source="synthetic nonlinear shear",
        features_train=features[:128],
        labels_train=labels[:128],
        features_calibration=features[128:256],
        labels_calibration=labels[128:256],
        features_test=features[256:],
        labels_test=labels[256:],
        predicate="inside_unit_radius",
        test_surface="radial boundary transition consequence",
        stability_condition="disjoint train/calibration/test split",
        gap_policy="non-singleton conformal sets are ledgered as gap",
    )


def test_lccp_certifies_singleton_claims_or_ledgers_gap():
    certificate = certify_latent_claim(_synthetic_split())

    assert certificate["claim_status"] in {"certified", "coverage_gap"}
    assert certificate["alpha"] == PRIMARY_ALPHA
    assert len(certificate["sweep"]) == len(ALPHAS)
    primary = certificate["primary"]
    assert primary["unlogged_error"] <= PRIMARY_ALPHA
    assert primary["conformal_miscoverage"] <= PRIMARY_ALPHA + 0.08
    assert 0.0 <= primary["certified_coverage"] <= 1.0
    assert certificate["debt_decomposition"]["coverage_debt"] == 1.0 - primary["certified_coverage"]
    assert "singleton conformal label" in certificate["claim_rule"]


def test_lccp_records_source_gap_without_fabricating_certificate():
    gap = source_gap_claim(
        carrier_id="frozen-carrier",
        source="missing-source",
        predicate="has_key",
        test_surface="pickup intervention",
        stability_condition="inventory-state split",
        reason="inventory source split is absent",
    )

    assert gap["claim_status"] == "source_gap"
    assert gap["primary"] is None
    assert gap["sweep"] == []
    assert gap["debt_decomposition"]["source_debt"] == 1.0
    assert "certified operational claim" in gap["cannot_claim"]


def test_lccp_default_artifacts_are_fail_closed():
    certificates, sweep, audit = build_latent_claim_certificate_artifacts(
        train_count=32,
        calibration_count=32,
        test_count=32,
    )

    assert certificates["schema_id"] == "bedc-latent-claim-certificates"
    assert sweep["schema_id"] == "bedc-conformal-gap-sweep"
    assert audit["schema_id"] == "bedc-claim-boundary-audit"
    assert {claim["predicate"] for claim in certificates["claims"]} >= {
        "door_key_context_visible",
        "has_key",
        "door_open_or_unlocked",
        "goal_reachable_with_current_state",
    }
    source_gap_claims = [claim for claim in certificates["claims"] if claim["claim_status"] == "source_gap"]
    assert source_gap_claims
    assert audit["gap_claim_count"] >= 1.0
    for row in audit["audit_checks"]:
        assert row["latent_carrier_frozen"] is True
        assert row["test_surface_declared"] is True
        if row["accepted_as_operational_name"]:
            assert row["conformal_miscoverage_within_alpha"] is True
        if row["predicate"] != "door_key_context_visible":
            assert row["fail_closed_gap_recorded"] is True

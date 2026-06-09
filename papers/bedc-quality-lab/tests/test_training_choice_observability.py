import json
from pathlib import Path

import bedc_quality_lab
import numpy as np
import pytest
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_training_choice_observability as runner


def _stat(mean, low=None, high=None):
    low = mean if low is None else low
    high = mean if high is None else high
    return {
        "n": 4,
        "mean": float(mean),
        "std": 0.0,
        "ci95_half_width": 0.0,
        "ci95_low": float(low),
        "ci95_high": float(high),
    }


def _aggregate(
    *,
    learned_auroc=0.86,
    learned_auroc_low=0.84,
    matched_auroc=0.50,
    matched_auroc_high=0.52,
    learned_reduction=0.22,
    learned_reduction_low=0.20,
    matched_reduction=0.01,
    matched_reduction_high=0.02,
):
    return {
        "record_count": 4,
        "seed_order": [1, 2, 3, 4],
        "by_arm": {
            "vanilla": {
                "failure_detection_auroc": _stat(0.50),
                "unlogged_error_rate": _stat(0.30),
            },
            "learned_gap_head_on_h": {
                "failure_detection_auroc": _stat(
                    learned_auroc, learned_auroc_low, learned_auroc + 0.02
                ),
                "unlogged_error_rate": _stat(0.08),
                "unlogged_error_reduction": _stat(
                    learned_reduction, learned_reduction_low, learned_reduction + 0.02
                ),
            },
            runner.MATCHED_RANDOM_ARM: {
                "failure_detection_auroc": _stat(
                    matched_auroc, matched_auroc - 0.02, matched_auroc_high
                ),
                "unlogged_error_rate": _stat(0.29),
                "unlogged_error_reduction": _stat(
                    matched_reduction, matched_reduction - 0.01, matched_reduction_high
                ),
            },
        },
    }


def _protocol(seed=1, split_delta=0):
    return {
        "seed": seed,
        "sample_count": runner.SAMPLE_COUNT,
        "rho": runner.RHO,
        "train_index_checksum": 100 + split_delta,
        "eval_index_checksum": 200 + split_delta,
        "train_count": 268,
        "eval_count": 116,
        "overlap_count": 0,
        "source_name": "gaussian-ou-toy-world",
        "latent_distribution": "gaussian",
        "mixing": "sinusoidal_shear",
        "model_loss_family": "tiny-encoder-representation-loss-or-deterministic-standardization",
        "inference_feature_builder": "scripts/run_gap_ledger_head_on_h.py::_build_inference_features",
    }


def _spec(**overrides):
    values = {
        "arm_id": "adamw_undertrained",
        "role": "training_choice_candidate",
        "training_family": "align-cov-mean",
        "optimizer_family": "AdamW",
        "steps": runner.UNDERTRAINED_STEPS,
        "lr": runner.LR,
        "weight_decay": runner.WEIGHT_DECAY,
        "use_torch": True,
        "ledger_certificate_steps": runner.UNDERTRAINED_STEPS,
        "boundary_when_unavailable": True,
        "declared_training_choice_axis": "steps",
    }
    values.update(overrides)
    return runner.TrainingChoiceArmSpec(**values)


def test_arm_protocol_requires_paired_source_split_and_only_declared_axis():
    reference = _spec(arm_id="adamw_reference", role="torch_reference", steps=80, ledger_certificate_steps=80)
    candidate = _spec(steps=8, ledger_certificate_steps=8)

    passed = runner._protocol_audit(
        {1: _protocol(1), 2: _protocol(2)},
        {1: _protocol(1), 2: _protocol(2)},
        reference,
        candidate,
    )
    assert passed["status"] == "pass"
    assert passed["changed_training_choice_fields"] == ["steps"]

    split_fail = runner._protocol_audit(
        {1: _protocol(1)},
        {1: _protocol(1, split_delta=1)},
        reference,
        candidate,
    )
    assert split_fail["status"] == "fail"

    lr_and_steps = _spec(steps=8, lr=runner.LR * 2.0)
    axis_fail = runner._protocol_audit({1: _protocol(1)}, {1: _protocol(1)}, reference, lr_and_steps)
    assert axis_fail["status"] == "fail"
    assert set(axis_fail["changed_training_choice_fields"]) == {"steps", "lr"}


def test_hardgates_pass_gives_observed_debt():
    gates = runner._hardgates(
        protocol_audit={"status": "pass"},
        aggregate=_aggregate(),
        feature_audit={"status": "pass", "forbidden_present": []},
    )
    ledger = {"status": "open"}

    assert all(gate["status"] == "pass" for gate in gates.values())
    assert runner._classification(hardgates=gates, ledger_item=ledger) == "observed-debt"


def test_failed_hardgate_with_open_ledger_is_ledger_risk_only():
    gates = runner._hardgates(
        protocol_audit={"status": "pass"},
        aggregate=_aggregate(learned_auroc=0.55, learned_auroc_low=0.53),
        feature_audit={"status": "pass", "forbidden_present": []},
    )

    assert gates["HG-TCO-2"]["status"] == "fail"
    assert runner._classification(hardgates=gates, ledger_item={"status": "open"}) == "ledger-risk-only"


def test_matched_random_positive_or_forbidden_feature_is_invalid_non_claim():
    matched_positive = runner._hardgates(
        protocol_audit={"status": "pass"},
        aggregate=_aggregate(matched_auroc=0.76, matched_auroc_high=0.78),
        feature_audit={"status": "pass", "forbidden_present": []},
    )
    assert matched_positive["HG-TCO-5"]["status"] == "fail"
    assert runner._classification(hardgates=matched_positive, ledger_item={"status": "open"}) == "invalid_non_claim"

    forbidden = runner._hardgates(
        protocol_audit={"status": "pass"},
        aggregate=_aggregate(),
        feature_audit={"status": "fail", "forbidden_present": ["z"]},
    )
    assert forbidden["HG-TCO-4"]["status"] == "fail"
    assert runner._classification(hardgates=forbidden, ledger_item={"status": "open"}) == "invalid_non_claim"


def test_forbidden_column_audit_reuses_h_feature_audit():
    assert runner._feature_audit(["h:0", "score:latent_x_positive"])["status"] == "pass"

    failed = runner._feature_audit(["h:0", "prediction_error"])
    assert failed["status"] == "fail"
    assert failed["forbidden_present"] == ["prediction_error"]
    assert failed["failed_gate"] == "forbidden-inference-column"

    label_failed = runner._feature_audit(["h:0", "label"])
    assert label_failed["status"] == "fail"
    assert label_failed["forbidden_present"] == ["label"]

    metadata_failed = runner._feature_audit(["h:0", "config_metadata.seed"])
    assert metadata_failed["status"] == "fail"
    assert metadata_failed["forbidden_present"] == ["config_metadata.seed"]


def test_torch_off_target_intervention_reencodes_changed_observations(monkeypatch):
    apply_inputs = []

    monkeypatch.setattr(runner, "_fit_torch_encoder", lambda **kwargs: ("encoder", "device"))

    def fake_apply_torch_encoder(*, encoder, device, all_x, all_x_pair):
        apply_inputs.append(np.asarray(all_x, dtype=np.float64).copy())
        return np.asarray(all_x, dtype=np.float64), np.asarray(all_x_pair, dtype=np.float64)

    monkeypatch.setattr(runner, "_apply_torch_encoder", fake_apply_torch_encoder)
    spec = _spec(steps=0, ledger_certificate_steps=0)

    surface = runner._surface_for_seed(spec=spec, seed=11)

    assert surface["gap_label_rates"]["off_target_intervention"] > 0.0
    assert len(apply_inputs) == 1 + len(runner.distinction.DISTINCTIONS)
    assert any(not np.array_equal(apply_inputs[0], changed) for changed in apply_inputs[1:])


def test_strict_conjunction_blocks_positive_when_reduction_gate_fails():
    gates = runner._hardgates(
        protocol_audit={"status": "pass"},
        aggregate=_aggregate(learned_reduction=0.01, learned_reduction_low=0.0, matched_reduction_high=0.02),
        feature_audit={"status": "pass", "forbidden_present": []},
    )

    assert gates["HG-TCO-2"]["status"] == "pass"
    assert gates["HG-TCO-3"]["status"] == "fail"
    assert runner._classification(hardgates=gates, ledger_item={"status": "open"}) == "ledger-risk-only"


def test_torch_unavailable_is_boundary_only_non_positive(monkeypatch):
    monkeypatch.setattr(runner, "_run_record", lambda **kwargs: (_ for _ in ()).throw(RuntimeError("no torch")))

    reference = _spec(arm_id="adamw_reference", role="torch_reference", steps=80, ledger_certificate_steps=80)
    result = runner._arm_result(
        spec=_spec(),
        reference_spec=reference,
        reference_protocols={1: _protocol(1)},
    )

    assert result["classification"] == "boundary-only"
    assert all(gate["status"] == "boundary" for gate in result["hardgates"].values())


def test_sidecar_schema_and_canonical_boundaries():
    assert runner.JSON_ARTIFACT == "runs/training_choice_observability.json"
    assert runner.REPORT_ARTIFACT == "runs/training_choice_observability.md"
    assert runner.LOCAL_SCHEMA_ID != SCHEMA_ID
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    canonical_blob = json.dumps([spec.__dict__ for spec in canonical.CANONICAL_REPORTS])
    assert "training_choice_observability" not in canonical_blob


def test_payload_has_no_hidden_weight_or_total_score_and_keeps_source_api(monkeypatch):
    reference = _spec(
        arm_id=runner.REFERENCE_ARM_ID,
        role="reference",
        training_family="deterministic-standardization",
        optimizer_family="none",
        steps=0,
        lr=0.0,
        weight_decay=0.0,
        use_torch=False,
        ledger_certificate_steps=0,
        boundary_when_unavailable=False,
        declared_training_choice_axis="training_family",
    )
    adamw = _spec(arm_id="adamw_reference", role="torch_reference", steps=80, ledger_certificate_steps=80)
    weak = _spec()
    monkeypatch.setattr(runner, "training_choice_arms", lambda: (reference, adamw, weak))

    def fake_record(spec, seed, seed_index):
        return {
            "seed": seed,
            "protocol": _protocol(seed),
            "feature_audit": {"status": "pass", "forbidden_present": []},
            "feature_columns": ["h:0"],
            "arms": {},
            "comparison": {},
        }

    monkeypatch.setattr(runner, "_run_record", fake_record)
    monkeypatch.setattr(runner, "_aggregate", lambda records: _aggregate())

    payload = runner.build_payload(generated_at="fixture-time")
    text = json.dumps(payload).lower()

    assert payload["canonical_role"] == runner.CANONICAL_ROLE
    assert payload["schema_id"] == runner.LOCAL_SCHEMA_ID
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert "total_score" not in text
    assert "rank_score" not in text
    assert "hidden_weight" not in text
    for term in runner.FORBIDDEN_POSITIVE_CLAIM_TERMS:
        assert term not in text
    assert "scripts/run_training_choice_observability.py" in payload["source_artifacts"]["generation_script"]


def test_torch_candidate_protocol_audit_uses_adamw_reference(monkeypatch):
    reference = _spec(
        arm_id=runner.REFERENCE_ARM_ID,
        role="reference",
        training_family="deterministic-standardization",
        optimizer_family="none",
        steps=0,
        lr=0.0,
        weight_decay=0.0,
        use_torch=False,
        ledger_certificate_steps=0,
        boundary_when_unavailable=False,
        declared_training_choice_axis="training_family",
    )
    adamw = _spec(arm_id="adamw_reference", role="torch_reference", steps=80, ledger_certificate_steps=80)
    weak = _spec()
    monkeypatch.setattr(runner, "training_choice_arms", lambda: (reference, adamw, weak))

    def fake_record(spec, seed, seed_index):
        split_delta = 0 if spec.arm_id == runner.REFERENCE_ARM_ID else 7
        return {
            "seed": seed,
            "protocol": _protocol(seed, split_delta=split_delta),
            "feature_audit": {"status": "pass", "forbidden_present": []},
            "feature_columns": ["h:0"],
            "arms": {},
            "comparison": {},
        }

    monkeypatch.setattr(runner, "_run_record", fake_record)
    monkeypatch.setattr(runner, "_aggregate", lambda records: _aggregate())

    payload = runner.build_payload(generated_at="fixture-time")
    weak_result = next(
        arm
        for arm in payload["training_choice_observability"]["arms"]
        if arm["arm_id"] == "adamw_undertrained"
    )

    assert weak_result["hardgates"]["HG-TCO-1"]["status"] == "pass"
    assert weak_result["hardgates"]["HG-TCO-1"]["audit"]["protocol_mismatches"] == []


def test_write_artifacts_targets_runs(tmp_path):
    payload = {
        "schema_id": runner.LOCAL_SCHEMA_ID,
        "artifact_id": runner.ARTIFACT_ID,
        "status": "pointer-only",
        "canonical_role": runner.CANONICAL_ROLE,
        "not_claimed": list(runner.NOT_CLAIMED),
        "revoke_conditions": list(runner.REVOKE_CONDITIONS),
        "training_choice_observability": {
            "arms": [
                {
                    "arm_id": "fixture",
                    "classification": "ledger-risk-only",
                    "ledger_item": {"status": "open"},
                    "hardgates": {"HG-TCO-1": {"status": "fail"}},
                }
            ]
        },
    }

    runner.write_artifacts(payload, root=tmp_path)

    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()
    assert str(Path(runner.JSON_ARTIFACT).parent) == "runs"

import json

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_gated_transformer as dgt


def test_dgt_replay_is_deterministic_and_loss_decreases():
    first = dgt.build_payload(generated_at="fixture-time", sidecar=canonical._build_new_model_hardgates_payload())
    second = dgt.build_payload(generated_at="fixture-time", sidecar=canonical._build_new_model_hardgates_payload())

    assert first == second
    assert first["training_evidence"]["loss_decrease"]["decreased"] is True
    assert first["prototype_status"] == "prototype-candidate"


def test_dgt_candidate_beats_controls_on_id_and_ood_surfaces():
    payload = dgt.build_payload(generated_at="fixture-time", sidecar=canonical._build_new_model_hardgates_payload())
    deltas = payload["classifier_surface_delta"]

    assert set(deltas["candidate_accuracy"]) == {"id_length_6", "ood_length_8", "ood_length_10", "stress_repeat_edge"}
    for surface, candidate_accuracy in deltas["candidate_accuracy"].items():
        assert candidate_accuracy > deltas["best_baseline_accuracy"][surface]
    assert payload["net_positive_signal"]["candidate_loss_beats_best_baseline_on_all_surfaces"] is True


def test_dgt_validator_resolves_all_gate_pointers(tmp_path):
    sidecar = canonical._build_new_model_hardgates_payload(generated_at="fixture-time")
    payload = dgt.build_payload(generated_at="fixture-time", sidecar=sidecar)
    validation = dgt.validate_dgt_new_model_gates(sidecar, payload)

    assert validation["status"] == "pass"
    assert {row["status"] for row in validation["gate_rows"].values()} == {"pass"}
    dgt.write_artifacts(payload, root=tmp_path)
    canonical._write_json_atomic(tmp_path / dgt.CANONICAL_JSON_ARTIFACT, payload)
    assert resolve_artifact_pointer(tmp_path, payload["claim_capsule_ref"]["artifact"] + ":$") is not None


def test_dgt_negative_witness_and_forbidden_audit_demote():
    payload = dgt.build_payload(generated_at="fixture-time", sidecar=canonical._build_new_model_hardgates_payload())
    assert {row["status"] for row in payload["revocation_rows"]} == {"demoted"}
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["forbidden_claim_term_audit"]["status"] = "demote"
    mutated["hardgate_instances"]["NEW-MODEL-HG17"]["status"] = "fail"
    mutated["prototype_status"] = "prototype-candidate"
    try:
        dgt.validate_payload(mutated)
    except ValueError as exc:
        assert "prototype status" in str(exc)
    else:
        raise AssertionError("mutated DGT payload should fail validation")

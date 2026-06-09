from __future__ import annotations

import json
from copy import deepcopy

import pytest

import bedc_quality_lab.discovery_regularized_training as drt
from bedc_quality_lab.discovery_regularized_training import (
    DEFAULT_ARMS,
    DEFAULT_DISCOVERY_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    DRIFT_TOLERANCE,
    DGT_REPLAY_HARDGATES,
    DGT_REPLAY_OWNER_READY_GATE,
    FORMAL_REPLAY_ARMS,
    DiscoveryRegularizedTrainingProjection,
    TorchTrainingArmProtocol,
    default_grid,
    drt_extension_forbidden_key_audit,
)
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_regularized_training as runner
from bedc_quality_lab.mechanism_dna import JSON_ARTIFACT as MECHANISM_DNA_ARTIFACT
from bedc_quality_lab.mechanism_dna import build_mechanism_dna, mechanism_dna_artifacts


REQUIRED_SUMMARY_KEYS = {
    "schema_id",
    "artifact_id",
    "generated_at",
    "run_id",
    "producer",
    "projector",
    "run_artifacts",
    "source_artifacts",
    "config",
    "grid",
    "records",
    "surface_registry",
    "lambda_summary",
    "constraint_summary",
    "arm_protocol",
    "replay_arm_catalog",
    "comparison_owner",
    "training_replay_bridge",
    "device_protocol",
    "compute_ledger",
    "torch_training_evidence",
    "negative_witness_mutations",
    "training_loop_trace",
    "matched_random_control",
    "quality_promotion_boundary",
    "certificate_guided_dn_preservation",
    "mechanism_ablation",
    "training_mechanism_cert",
    "loss_family",
    "component_ablation",
    "training_method_comparison",
    "drt_extension_hardgates",
    "jet_loss_protocol",
    "jet_loss_surface",
    "jet_ablation",
    "jet_loss_frontier",
    "jet_sidecar_artifacts",
    "hardgate",
    "failed_gate",
    "discovery_map_signal",
    "dgt_replay_gate_summary",
    "dgt_replay_claim_status",
    "positive_claim",
    "claim_capsule_ref",
    "not_claimed",
    "what_was_learned",
    "revocation_rows",
    "forbidden_claim_term_audit",
}


def _project(records=None, **config):
    run_id = config.pop("run_id", "fixture-discovery-regularized-training")
    artifacts = {
        "summary": f"reports/runs/{run_id}/summary.json",
        "claim_capsule": f"reports/runs/{run_id}/claim_capsule.json",
        "raw_metrics": f"reports/runs/{run_id}/raw_metrics.jsonl",
        "report": f"reports/runs/{run_id}/report.md",
    }
    full_config = {
        "run_id": run_id,
        "discovery_lambdas": list(DEFAULT_DISCOVERY_LAMBDAS),
        "rhos": list(DEFAULT_RHOS),
        "mixings": list(DEFAULT_MIXINGS),
        "seeds": list(DEFAULT_SEEDS),
        "arms": list(DEFAULT_ARMS),
        "requested_device": "mps",
        "resolved_device": "cpu",
        "torch_status": "unavailable",
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": {"torch": "fixture"},
        "steps": 12,
        **config,
    }
    return DiscoveryRegularizedTrainingProjection(
        config=full_config,
        records=_fixture_records() if records is None else records,
        generated_at="fixture-time",
        run_artifacts=artifacts,
    ).project()


def _mechanism_dna_context(overrides=None):
    source_payloads = {
        artifact: json.loads((canonical.ROOT / artifact).read_text(encoding="utf-8"))
        for artifact in mechanism_dna_artifacts()
    }
    source_payloads.update(overrides or {})
    return {
        "reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]},
        **source_payloads,
        MECHANISM_DNA_ARTIFACT: build_mechanism_dna(
            source_payloads,
            generated_at="fixture-time",
            deterministic_seed=935,
        ),
    }


def _torch_fixture_records():
    rows = []
    for discovery_lambda in (0.001, 0.005):
        for rho in (0.7, 0.9):
            for seed in (11, 23):
                for arm in ("drt", "matched_random"):
                    row = runner.deterministic_record(discovery_lambda, rho, "spiral", seed, arm)
                    row.update(
                        {
                            "backend": "torch-training-arm",
                            "internal_metric_alias": arm,
                            "resolved_device": "cpu",
                            "steps": 12,
                            "dtype": "float32",
                            "torch_protocol": {
                                "requested_device": "mps",
                                "resolved_device": "cpu",
                                "seed": seed,
                                "steps": 12,
                                "dtype": "float32",
                                "drift_tolerance": DRIFT_TOLERANCE,
                                "status": "available",
                            },
                        }
                    )
                    rows.append(row)
    return rows


def _fixture_records():
    return [
        *runner.collect_deterministic_records(),
        *runner.collect_mechanism_ablation_records(),
        *_torch_fixture_records(),
    ]


def _recursive_keys(value):
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_recursive_keys(item))
        return keys
    if isinstance(value, list):
        keys = set()
        for item in value:
            keys.update(_recursive_keys(item))
        return keys
    return set()


def _recursive_pointer_fields(value, path="$"):
    if isinstance(value, dict):
        found = []
        for key, item in value.items():
            child_path = f"{path}.{key}"
            if isinstance(key, str) and key.endswith("_pointer"):
                found.append((child_path, item))
            found.extend(_recursive_pointer_fields(item, child_path))
        return found
    if isinstance(value, list):
        found = []
        for index, item in enumerate(value):
            found.extend(_recursive_pointer_fields(item, f"{path}.{index}"))
        return found
    return []


def test_default_deterministic_grid_has_expected_anchor_size():
    assert len(default_grid()) == 2160
    assert len(runner.collect_deterministic_records()) == 2160


def test_deterministic_replay_and_required_keys():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first["summary_payload"], sort_keys=True) == json.dumps(second["summary_payload"], sort_keys=True)
    assert REQUIRED_SUMMARY_KEYS <= set(first["summary_payload"])
    assert first["summary_payload"]["grid"]["record_count"] == 2160
    assert first["summary_payload"]["grid"]["expected_record_count"] == 2160
    assert first["summary_payload"]["run_artifacts"]["raw_metrics"] == first["summary_payload"]["records"]["raw_rows_pointer"]


def test_formal_replay_arms_and_gate_summary_are_canonical(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps")["summary_payload"]

    assert tuple(summary["arm_protocol"]["formal_replay"]["arms"]) == FORMAL_REPLAY_ARMS
    assert "compat_aliases" not in summary["arm_protocol"]["formal_replay"]
    assert "compat_aliases" not in summary["replay_arm_catalog"]
    assert [row["arm_id"] for row in summary["replay_arm_catalog"]["formal_arms"]] == list(FORMAL_REPLAY_ARMS)
    assert [row["arm_id"] for row in summary["training_replay_bridge"]["rows"]] == list(FORMAL_REPLAY_ARMS)
    assert summary["training_replay_bridge"]["full_arm"]["arm_id"] == "DGT_full"
    assert summary["training_replay_bridge"]["matched_random_arm"]["arm_id"] == "matched_random_structural_control"
    assert summary["training_replay_bridge"]["matched_random_arm"]["classifier_shift_count_mean"] == 0.0
    assert summary["dgt_replay_gate_summary"]["gate_order"] == [
        DGT_REPLAY_OWNER_READY_GATE,
        *DGT_REPLAY_HARDGATES,
    ]
    assert summary["dgt_replay_gate_summary"]["status"] == "pass"
    assert summary["dgt_replay_claim_status"]["level_candidate"] == "D5-M"


def _dgt_replay_summary_after_mutation(summary, mutate, monkeypatch):
    mutated = deepcopy(summary)
    projection = DiscoveryRegularizedTrainingProjection(
        config=mutated["config"],
        records=_fixture_records(),
        generated_at="fixture-time",
        run_artifacts=mutated["run_artifacts"],
    )
    mutate(mutated, monkeypatch)
    hardgates = projection.hardgate_verdicts(mutated, mutated["quality_promotion_boundary"])
    mutated["hardgate"] = {
        "status": "pass" if all(row.get("status") == "pass" for row in hardgates.values()) else "fail",
        "gates": hardgates,
        "failed_gate": projection.failed_gate(hardgates),
    }
    mutated["failed_gate"] = mutated["hardgate"]["failed_gate"]
    mutated["dgt_replay_gate_summary"] = drt.dgt_replay_gate_summary(mutated)
    mutated["discovery_map_signal"] = projection.discovery_map_signal(hardgates)
    return mutated


def _remove_replay_catalog_arm(summary, _monkeypatch):
    summary["replay_arm_catalog"]["formal_arms"].pop()


def _remove_replay_bridge_row(summary, _monkeypatch):
    summary["training_replay_bridge"]["rows"].pop()


def _break_replay_parameter_count(summary, _monkeypatch):
    summary["training_replay_bridge"]["rows"][0]["parameter_count"] = 144001


def _break_replay_compute_budget(summary, _monkeypatch):
    summary["training_replay_bridge"]["rows"][0]["compute_budget"] = 0.5


def _break_matched_randomization(summary, _monkeypatch):
    summary["training_replay_bridge"]["matched_random_arm"]["structural_randomized"] = False


def _break_full_classifier_shift(summary, _monkeypatch):
    summary["training_replay_bridge"]["full_arm"]["classifier_shift_count_mean"] = 0.0


def _break_full_net_positive_signal(summary, _monkeypatch):
    summary["training_replay_bridge"]["full_arm"]["net_positive_signal"] = False


def _break_matched_random_shift(summary, _monkeypatch):
    summary["training_replay_bridge"]["matched_random_arm"]["classifier_shift_count_mean"] = 1.0


def _break_compute_ledger(summary, _monkeypatch):
    summary["compute_ledger"]["status"] = "incomplete"


def _break_forbidden_claim_audit(_summary, monkeypatch):
    monkeypatch.setattr(
        drt,
        "POSITIVE_CLAIM",
        {
            **drt.POSITIVE_CLAIM,
            "text": f"{drt.POSITIVE_CLAIM['text']} {drt.FORBIDDEN_POSITIVE_CLAIM_TERMS[0]}",
        },
    )


@pytest.mark.parametrize(
    ("gate", "mutate"),
    [
        ("DGT-REPLAY-HG1", _remove_replay_catalog_arm),
        ("DGT-REPLAY-HG2", _remove_replay_bridge_row),
        ("DGT-REPLAY-HG3", _break_replay_parameter_count),
        ("DGT-REPLAY-HG4", _break_replay_compute_budget),
        ("DGT-REPLAY-HG5", _break_matched_randomization),
        ("DGT-REPLAY-HG6", _break_full_classifier_shift),
        ("DGT-REPLAY-HG7", _break_full_net_positive_signal),
        ("DGT-REPLAY-HG8", _break_matched_random_shift),
        ("DGT-REPLAY-HG9", _break_compute_ledger),
        ("DGT-REPLAY-HG10", _break_forbidden_claim_audit),
    ],
)
def test_dgt_replay_hardgate_failures_demote_to_dn(monkeypatch, gate, mutate):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps")["summary_payload"]
    mutated = _dgt_replay_summary_after_mutation(summary, mutate, monkeypatch)

    assert mutated["hardgate"]["gates"][gate]["status"] == "fail"
    assert mutated["hardgate"]["failed_gate"] == gate
    assert mutated["dgt_replay_gate_summary"]["status"] == "fail"
    assert mutated["dgt_replay_gate_summary"]["failed_gate"] == gate
    assert mutated["dgt_replay_gate_summary"]["level_candidate"] == "DN"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert mutated["discovery_map_signal"]["failed_gate"] == gate


def test_dgt_replay_wp1_owner_missing_blocks_to_dn(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(
        generated_at="fixture-time",
        requested_device="mps",
        source_artifacts={"model_comparison": {"status": "missing"}},
    )["summary_payload"]

    assert summary["comparison_owner"]["status"] == "missing"
    assert summary["hardgate"]["failed_gate"] == DGT_REPLAY_OWNER_READY_GATE
    assert summary["dgt_replay_gate_summary"]["status"] == "blocked"
    assert summary["dgt_replay_gate_summary"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"


def test_torch_unavailable_boundary_records_device_and_fails_hg6_to_dn():
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=False)["summary_payload"]

    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "not-requested"
    assert summary["device_protocol"]["drift_tolerance"] == pytest.approx(1.0e-4)
    assert summary["torch_training_evidence"]["status"] == "unavailable"
    assert summary["torch_training_evidence"]["row_count"] == 0
    assert summary["hardgate"]["status"] == "fail"
    assert summary["hardgate"]["failed_gate"] == "DRT-HG6"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"


def test_torch_available_fixture_promotes_d5m_and_records_payload_sections(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps")["summary_payload"]

    assert summary["torch_training_evidence"]["status"] == "available"
    assert summary["torch_training_evidence"]["row_count"] == 16
    assert summary["torch_training_evidence"]["expected_row_count"] == 16
    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "cpu"
    protocol = summary["torch_training_evidence"]["protocols"][0]
    assert set(protocol) == set(TorchTrainingArmProtocol.__dataclass_fields__)
    assert protocol["requested_device"] == "mps"
    assert protocol["resolved_device"] == "cpu"
    assert protocol["drift_tolerance"] == pytest.approx(1.0e-4)
    assert summary["hardgate"]["gates"]["DRT-HG6"]["status"] == "pass"
    assert summary["hardgate"]["failed_gate"] is None
    assert summary["discovery_map_signal"]["level_candidate"] == "D5-M"
    assert summary["discovery_map_signal"]["status"] == "d5-m-candidate"
    assert summary["discovery_map_signal"]["evidence_pointer"] == "$.training_mechanism_cert"
    assert summary["training_loop_trace"]["retrain_rows_pointer"] == "$.torch_training_evidence"
    assert summary["negative_witness_mutations"]["failed_gate_pointer"] == "$.hardgate.status"
    assert summary["drt_extension_hardgates"]["status"] == "pass"
    assert summary["hardgate"]["gates"]["DRT-HG7"]["status"] == "pass"
    assert summary["hardgate"]["gates"]["DRT-HG7"]["evidence_pointer"] == "$.certificate_guided_dn_preservation"
    assert summary["hardgate"]["gates"]["DRT-HG8"]["status"] == "pass"
    assert summary["hardgate"]["gates"]["DRT-HG8"]["evidence_pointer"] == "$.mechanism_ablation"
    assert summary["hardgate"]["gates"]["DRT-HG9"]["status"] == "pass"
    assert summary["hardgate"]["gates"]["DRT-HG9"]["evidence_pointer"] == "$.training_mechanism_cert"
    assert summary["training_mechanism_cert"]["status"] == "pass"
    assert summary["training_mechanism_cert"]["hardgate_pointer"].endswith("$.hardgate.gates.DRT-HG9")
    assert summary["mechanism_ablation"]["status"] == "pass"
    preservation = summary["certificate_guided_dn_preservation"]
    assert preservation["status"] == "pass"
    assert {row["artifact"] for row in preservation["required_refs"]} == {
        "reports/canonical/certificate-guided-training.json",
        "reports/canonical/certificate-guided-discovery.json",
    }
    assert all(row["expected_discovery_level"] == "DN" for row in preservation["required_refs"])
    assert all(row["expected_discovery_level"] == "DN" for row in preservation["discovery_map_refs"])
    assert "terminal_verdict" not in json.dumps(preservation, sort_keys=True)
    assert "metrics" not in preservation
    assert len(summary["mechanism_ablation"]["comparisons"]) == 6
    assert set(summary["loss_family"]["terms"]) == {
        "discovery",
        "ledger",
        "certificate",
        "mechanism",
        "cost",
        "negative_witness",
    }
    assert len(summary["component_ablation"]["rows"]) == 7
    assert summary["training_method_comparison"]["metric_pointers"]["uer"].endswith("$.records.extension_metrics.uer_mean")
    assert "terminal_verdict" not in json.dumps(summary, sort_keys=True)


def test_drt_compute_ledger_is_required_summary(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps")["summary_payload"]
    ledger = summary["compute_ledger"]

    assert "compute_ledger" in REQUIRED_SUMMARY_KEYS
    assert ledger["status"] == "complete"
    assert ledger["cost_protocol_pointer"] == "$.source_artifacts.cost_protocol"
    assert ledger["deterministic_seed_count"] > 0
    assert ledger["torch_seed_count"] > 0
    assert ledger["flops_proxy"] > 0


@pytest.mark.parametrize(
    ("mutate", "field"),
    [
        (lambda section: section["required_refs"].pop(), "required_refs_present"),
        (lambda section: section["required_refs"][0].update({"expected_discovery_level": "D4"}), "expected_dn_status"),
        (lambda section: section.update({"replacement_claim": "replace certificate-guided artifacts"}), "forbidden_actions_absent"),
        (lambda section: section.update({"terminal_verdict": "demoted"}), "terminal_status_isolated"),
    ],
)
def test_certificate_guided_dn_preservation_fail_cases(monkeypatch, mutate, field):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps")["summary_payload"]
    section = deepcopy(summary["certificate_guided_dn_preservation"])
    mutate(section)
    projection = DiscoveryRegularizedTrainingProjection(
        config=summary["config"],
        records=_fixture_records(),
        generated_at="fixture-time",
        run_artifacts=summary["run_artifacts"],
    )
    hardgates = projection.hardgate_verdicts(
        {**summary, "certificate_guided_dn_preservation": section},
        summary["quality_promotion_boundary"],
    )

    assert hardgates["DRT-HG7"]["status"] == "fail"
    assert hardgates["DRT-HG7"][field] is False
    assert projection.failed_gate(hardgates) == "DRT-HG7"


def test_certificate_guided_dn_preservation_missing_source_ref_fails_hg7(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    summary = _project(
        source_artifacts={"reports/canonical/certificate-guided-training.json": "missing"},
    )["summary_payload"]

    assert summary["certificate_guided_dn_preservation"]["status"] == "fail"
    assert summary["hardgate"]["gates"]["DRT-HG7"]["status"] == "fail"
    assert summary["hardgate"]["failed_gate"] == "DRT-HG7"


def test_compute_ledger_cost_protocol_pointer_is_fail_closed_in_ledger():
    projection = _project(source_artifacts={"cost_protocol": ""})
    summary = projection["summary_payload"]
    capsule = projection["claim_capsule_payload"]

    assert summary["source_artifacts"]["cost_protocol"] == ""
    assert summary["compute_ledger"]["status"] == "incomplete"
    assert "cost_protocol_pointer" in summary["compute_ledger"]["missing_fields"]
    assert capsule["source_artifacts"]["cost_protocol"] == ""
    assert capsule["source_artifacts"]["cost_protocol"] == summary["source_artifacts"]["cost_protocol"]
    assert capsule["result_snapshot"]["compute_ledger"]["status"] == "incomplete"
    assert "cost_protocol_pointer" in capsule["result_snapshot"]["compute_ledger"]["missing_fields"]
    assert "configs/default_cost_protocol.yaml" not in json.dumps(capsule["source_artifacts"], sort_keys=True)


def test_drt_hg7_fails_when_steps_or_seed_counts_are_missing():
    zero_steps = _project(steps=0)["summary_payload"]

    assert zero_steps["compute_ledger"]["status"] == "incomplete"
    assert "steps" in zero_steps["compute_ledger"]["missing_fields"]

    missing_seed_records = deepcopy(_fixture_records())
    for row in missing_seed_records:
        if row.get("backend") == "deterministic-anchor":
            row.pop("seed", None)
            break
    missing_seed = _project(missing_seed_records)["summary_payload"]

    assert "deterministic_seed" in missing_seed["compute_ledger"]["missing_fields"]


def test_claim_capsule_carries_compute_ledger_snapshot_without_raw_rows():
    capsule = _project()["claim_capsule_payload"]
    ledger = capsule["result_snapshot"]["compute_ledger"]

    assert ledger["status"] == "complete"
    assert "raw_rows_pointer" not in ledger
    assert "protocols_pointer" not in ledger
    assert "evidence_pointer" not in ledger
    assert ledger["cost_protocol_pointer"] == "$.source_artifacts.cost_protocol"


def test_compute_ledger_is_replay_stable(monkeypatch):
    monkeypatch.setattr(runner, "collect_torch_records", lambda **_: (_torch_fixture_records(), "available", "cpu", {"torch": "fixture"}))
    first = runner.build_projection(generated_at="fixture-time")["summary_payload"]["compute_ledger"]
    second = runner.build_projection(generated_at="fixture-time")["summary_payload"]["compute_ledger"]

    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)


def test_compute_ledger_never_uses_refactor_loop_host_env():
    projection = _project()
    payload = {
        "source_artifacts": projection["summary_payload"]["source_artifacts"],
        "compute_ledger": projection["summary_payload"]["compute_ledger"],
        "claim_capsule": projection["claim_capsule_payload"],
    }

    assert ".refactor-loop/host.env" not in json.dumps(payload, sort_keys=True)


def test_drt_hg8_mechanism_ablation_passes_with_required_arms_and_resolved_pointers():
    summary = _project()["summary_payload"]
    mechanism = summary["mechanism_ablation"]

    assert set(mechanism) == {
        "schema_id",
        "backend",
        "anchor_cell",
        "required_arms",
        "metric_keys",
        "raw_rows_pointer",
        "full_drt",
        "by_arm",
        "comparisons",
        "status",
        "required_arms_present",
        "comparison_pointers_resolve",
        "full_beats_all_ablations",
        "full_positive_mechanism_signal",
        "no_ablation_net_positive_parity",
    }
    assert mechanism["status"] == "pass"
    assert mechanism["required_arms_present"] is True
    assert mechanism["comparison_pointers_resolve"] is True
    assert mechanism["full_beats_all_ablations"] is True
    assert mechanism["full_positive_mechanism_signal"] is True
    assert mechanism["no_ablation_net_positive_parity"] is True
    assert summary["hardgate"]["gates"]["DRT-HG8"]["status"] == "pass"
    for row in mechanism["comparisons"]:
        for pointer in row["comparison_pointers"].values():
            assert discovery_map.pointer_value(summary, pointer.split(":", 1)[1]) is not None


def test_drt_hg9_blocks_d5m_when_training_mechanism_cert_fails():
    records = deepcopy(_fixture_records())
    summary = _project(records)["summary_payload"]
    summary["training_mechanism_cert"]["status"] = "fail"
    summary["hardgate"]["gates"]["DRT-HG9"]["status"] = "fail"
    summary["hardgate"]["status"] = "fail"
    summary["discovery_map_signal"] = DiscoveryRegularizedTrainingProjection(
        config={},
        records=[],
        generated_at="fixture-time",
        run_artifacts={},
    ).discovery_map_signal(summary["hardgate"]["gates"])

    assert summary["hardgate"]["gates"]["DRT-HG9"]["status"] == "fail"
    assert summary["training_mechanism_cert"]["status"] == "fail"
    assert summary["failed_gate"] is None
    assert summary["discovery_map_signal"]["level_candidate"] == "D4"
    assert summary["discovery_map_signal"]["status"] == "d4-candidate"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG9"
    assert summary["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.DRT-HG9.status"


def test_drt_hg9_pass_cert_promotes_d5m_candidate():
    summary = _project()["summary_payload"]

    assert summary["training_mechanism_cert"]["status"] == "pass"
    assert summary["hardgate"]["gates"]["DRT-HG9"]["status"] == "pass"
    assert summary["discovery_map_signal"]["level_candidate"] == "D5-M"
    assert summary["discovery_map_signal"]["status"] == "d5-m-candidate"
    for row in summary["training_mechanism_cert"]["required_pointers"]:
        assert discovery_map.pointer_value(summary, row["pointer"].split(":", 1)[1]) is not None


def test_jet_protocol_is_single_source_for_sidecars(tmp_path):
    projection = _project()
    runner.write_artifacts(projection, root=tmp_path)
    summary = projection["summary_payload"]
    sidecar = json.loads((tmp_path / summary["jet_sidecar_artifacts"]["jet_loss_surface"]).read_text(encoding="utf-8"))
    frontier = json.loads((tmp_path / summary["jet_sidecar_artifacts"]["jet_loss_frontier"]).read_text(encoding="utf-8"))
    ablation = (tmp_path / summary["jet_sidecar_artifacts"]["jet_ablation"]).read_text(encoding="utf-8")

    assert sidecar["owner_artifact_id"] == summary["artifact_id"]
    assert sidecar["owner_protocol_pointer"].endswith("$.jet_loss_protocol")
    assert "thresholds" not in sidecar
    assert frontier["owner_protocol_pointer"].endswith("$.jet_loss_protocol")
    assert "owner_pointer" in ablation


def test_drtj_hg1_required_order_gain():
    summary = _project()["summary_payload"]
    gate = summary["hardgate"]["gates"]["DRTJ-HG1"]

    assert gate["status"] == "pass"
    assert gate["required_order_gain"] >= summary["jet_loss_protocol"]["thresholds"]["required_order_gain_min"]
    assert gate["matched_random_jet_gain"] <= summary["jet_loss_protocol"]["thresholds"]["matched_random_jet_gain_max"]

    records = _fixture_records()
    for row in records:
        if row.get("arm") == "DGT_full":
            row["jet_required_order_gain"] = row["jet_required_order_gain"] - 0.03
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRTJ-HG1"]["status"] == "fail"
    assert failed["failed_gate"] == "DRTJ-HG1"


def test_drtj_hg2_order_one_non_degradation():
    summary = _project()["summary_payload"]
    assert summary["hardgate"]["gates"]["DRTJ-HG2"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row.get("arm") == "DGT_full":
            row["jet_order_one_gain"] = -0.03
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRTJ-HG2"]["status"] == "fail"
    assert failed["failed_gate"] == "DRTJ-HG2"


def test_drtj_hg3_high_order_gain_not_shortcut_reducible():
    summary = _project()["summary_payload"]
    assert summary["hardgate"]["gates"]["DRTJ-HG3"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row.get("arm") == "DGT_full":
            row["shortcut_witness_flipped"] = True
            row["jet_shortcut_reducible_fraction"] = 0.92
    failed = _project(records)["summary_payload"]
    assert failed["jet_ablation"]["shortcut_control_not_reducible"] is False
    assert failed["hardgate"]["gates"]["DRTJ-HG3"]["status"] == "fail"
    assert failed["failed_gate"] == "DRTJ-HG3"


def test_drtj_hg4_matched_random_jet_control_negative():
    summary = _project()["summary_payload"]
    assert summary["hardgate"]["gates"]["DRTJ-HG4"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row.get("arm") == "matched_random_structural_control":
            row["jet_required_order_gain"] = 0.02
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRTJ-HG4"]["status"] == "fail"
    assert failed["failed_gate"] == "DRTJ-HG1"


def test_drtj_hg5_quality_q_ci_low_positive():
    summary = _project()["summary_payload"]
    assert summary["hardgate"]["gates"]["DRTJ-HG5"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row.get("arm") == "DGT_full":
            row["jet_quality_q_ci_low"] = -0.002
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRTJ-HG5"]["status"] == "fail"
    assert failed["failed_gate"] == "DRTJ-HG5"


def test_projection_rejects_d5m_claim_without_training_mechanism_cert():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    summary = _project()["summary_payload"]
    summary.pop("training_mechanism_cert")
    summary["hardgate"]["gates"].pop("DRT-HG9")

    projected = discovery_map.projection_payload(spec, summary)

    assert projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "DN"
    assert projected["main_verdict"]["discovery_regularized_training"]["status"] == "negative"


def test_drt_hg8_missing_mechanism_ablation_arm_demotes_to_dn():
    records = [
        row
        for row in _fixture_records()
        if row.get("backend") != "deterministic-mechanism-ablation"
        or row.get("arm") != "without_mechanism"
    ]
    summary = _project(records)["summary_payload"]

    assert summary["mechanism_ablation"]["status"] == "fail"
    assert summary["mechanism_ablation"]["required_arms_present"] is False
    assert summary["hardgate"]["gates"]["DRT-HG8"]["status"] == "fail"
    assert summary["failed_gate"] == "DRT-HG8"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.DRT-HG8.status"


def test_drt_hg8_fails_when_ablation_reaches_net_positive_parity():
    records = _fixture_records()
    for row in records:
        if row.get("backend") == "deterministic-mechanism-ablation" and row.get("arm") == "without_mechanism":
            row["quality_q"] = 0.1
            row["classifier_shift_count"] = 1
            row["net_positive_signal"] = True
    summary = _project(records)["summary_payload"]

    parity_row = next(row for row in summary["mechanism_ablation"]["comparisons"] if row["arm_id"] == "without_mechanism")
    assert parity_row["net_positive_parity"] is True
    assert summary["mechanism_ablation"]["no_ablation_net_positive_parity"] is False
    assert summary["mechanism_ablation"]["status"] == "fail"
    assert summary["failed_gate"] == "DRT-HG8"


def test_drt_hg8_fails_when_ablation_beats_full_drt():
    records = _fixture_records()
    for row in records:
        if row.get("backend") == "deterministic-mechanism-ablation" and row.get("arm") == "without_cost":
            row["quality_q"] = 0.9
    summary = _project(records)["summary_payload"]

    beaten_row = next(row for row in summary["mechanism_ablation"]["comparisons"] if row["arm_id"] == "without_cost")
    assert beaten_row["full_beats_ablation"] is False
    assert summary["mechanism_ablation"]["full_beats_all_ablations"] is False
    assert summary["mechanism_ablation"]["status"] == "fail"
    assert summary["failed_gate"] == "DRT-HG8"


def test_real_torch_training_records_protocol_and_classifier_surface_delta():
    pytest.importorskip("torch")
    rows, status, resolved_device, abi = runner.collect_torch_records(
        requested_device="cpu",
        steps=2,
        enabled=True,
        discovery_lambdas=(0.001,),
        rhos=(0.7,),
        seeds=(11,),
        arms=("drt", "matched_random"),
    )

    assert status == "available"
    assert resolved_device == "cpu"
    assert abi["torch"] != "fixture"
    assert len(rows) == 2
    assert {row["arm"] for row in rows} == {"drt", "matched_random"}

    by_arm = {row["arm"]: row for row in rows}
    drt = by_arm["drt"]
    matched = by_arm["matched_random"]
    for row in rows:
        assert row["backend"] == "torch-training-arm"
        assert row["seed"] == 11
        assert row["steps"] == 2
        assert row["dtype"] == "float32"
        assert row["resolved_device"] == "cpu"
        assert row["torch_protocol"] == {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "seed": 11,
            "steps": 2,
            "dtype": "float32",
            "drift_tolerance": DRIFT_TOLERANCE,
            "status": "available",
        }
    assert drt["classifier_shift_count"] == 1
    assert matched["classifier_shift_count"] == 0
    assert drt["net_positive_signal"] is True
    assert matched["net_positive_signal"] is False
    assert drt["delta_quality_ci_low"] > 0.0
    assert matched["delta_quality_ci_low"] < 0.0
    assert drt["certificate_loss"] < drt["matched_random_certificate_loss"]

    summary = _project(
        rows,
        requested_device="cpu",
        resolved_device=resolved_device,
        torch_status=status,
        steps=2,
        dependency_abi=abi,
    )["summary_payload"]
    evidence = summary["torch_training_evidence"]
    assert evidence["status"] == "available"
    assert evidence["row_count"] == 2
    assert evidence["expected_row_count"] == 16
    assert evidence["classifier_surface_delta"] == {
        "source_arm": "drt",
        "control_arm": "matched_random",
        "drt_classifier_shift_count_mean": 1.0,
        "matched_random_classifier_shift_count_mean": 0.0,
        "drt_minus_matched_random_classifier_shift_count": 1.0,
        "net_positive_signal": True,
    }
    assert summary["hardgate"]["gates"]["DRT-HG6"]["status"] == "fail"
    assert summary["hardgate"]["gates"]["DRT-HG6"]["row_count"] == 2
    assert summary["hardgate"]["gates"]["DRT-HG6"]["protocol_count"] == 2


def test_seed_idempotence_and_quantized_tolerance():
    first = runner.deterministic_record(0.001, 0.9, "spiral", 11, "drt")
    second = runner.deterministic_record(0.001, 0.9, "spiral", 11, "drt")
    other = runner.deterministic_record(0.001, 0.9, "spiral", 23, "drt")

    assert first == second
    assert abs(first["quality_q"] - round(first["quality_q"], 6)) <= DRIFT_TOLERANCE
    assert first["quality_q"] != other["quality_q"]


def test_drt_hg1_debt_down_benefit_down_demotes():
    records = _fixture_records()
    for row in records:
        if row["arm"] == "DGT_full":
            row["benefit_q"] = 0.1
    summary = _project(records)["summary_payload"]

    assert summary["hardgate"]["gates"]["DRT-HG1"]["status"] == "fail"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG1"


def test_drt_hg2_requires_positive_ci_low_and_benefit_nondecreasing():
    summary = _project()["summary_payload"]
    assert summary["lambda_summary"]["delta_quality_ci_low_positive"] is True
    assert summary["lambda_summary"]["benefit_nondecreasing"] is True
    assert summary["hardgate"]["gates"]["DRT-HG2"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row["arm"] == "DGT_full":
            row["delta_quality_ci_low"] = -0.001
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRT-HG2"]["status"] == "fail"
    assert failed["discovery_map_signal"]["failed_gate"] == "DRT-HG2"


def test_drt_hg3_classifier_shift_and_net_positive_signal():
    summary = _project()["summary_payload"]
    assert summary["surface_registry"]["classifier_shift"]["classifier_shift_positive"] is True
    assert summary["surface_registry"]["classifier_shift"]["net_positive_signal"] is True
    assert summary["hardgate"]["gates"]["DRT-HG3"]["status"] == "pass"

    records = _fixture_records()
    for row in records:
        if row["arm"] == "DGT_full":
            row["classifier_shift_count"] = 0
            row["net_positive_signal"] = False
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRT-HG3"]["status"] == "fail"


def test_drt_hg4_matched_random_certificate_loss_improvement_demotion():
    records = _fixture_records()
    for row in records:
        if row["arm"] == "matched_random_structural_control":
            row["certificate_loss"] = 0.01
    summary = _project(records)["summary_payload"]

    assert summary["matched_random_control"]["certificate_loss_improvement"] is False
    assert summary["hardgate"]["gates"]["DRT-HG4"]["status"] == "fail"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG4"


def test_drt_hg4_matched_random_control_positive_demotes_to_dn():
    summary = _project()["summary_payload"]
    matched = {**summary["matched_random_control"], "control_positive": True}
    projection = DiscoveryRegularizedTrainingProjection(
        config=summary["config"],
        records=[],
        generated_at="fixture-time",
        run_artifacts=summary["run_artifacts"],
    )
    hardgates = projection.hardgate_verdicts(
        {
            "constraint_summary": summary["constraint_summary"],
            "lambda_summary": summary["lambda_summary"],
            "surface_registry": summary["surface_registry"],
            "matched_random_control": matched,
                "torch_training_evidence": summary["torch_training_evidence"],
                "mechanism_ablation": summary["mechanism_ablation"],
                "compute_ledger": summary["compute_ledger"],
                "comparison_owner": summary["comparison_owner"],
                "replay_arm_catalog": summary["replay_arm_catalog"],
                "training_replay_bridge": summary["training_replay_bridge"],
            },
        summary["quality_promotion_boundary"],
    )
    signal = projection.discovery_map_signal(hardgates)

    assert hardgates["DRT-HG4"]["status"] == "fail"
    assert hardgates["DRT-HG4"]["evidence_pointer"] == "$.matched_random_control.control_positive"
    assert signal["failed_gate"] == "DRT-HG4"
    assert signal["level_candidate"] == "DN"


def test_drt_hg5_rejects_task_accuracy_only_rows():
    records = _fixture_records()
    for row in records:
        if row["arm"] == "base_transformer":
            row["net_positive_signal"] = True
            break
    summary = _project(records)["summary_payload"]

    assert summary["surface_registry"]["task_accuracy_only"]["task_accuracy_only_rejected"] is False
    assert summary["hardgate"]["gates"]["DRT-HG5"]["status"] == "fail"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG5"


def test_current_lab_projection_and_pointer_resolvability():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    summary = _project()["summary_payload"]
    context = _mechanism_dna_context({runner.JSON_ARTIFACT: summary})
    row = discovery_map.discovery_row(spec, summary, context)
    projected = discovery_map.projection_payload(spec, summary, context)

    assert projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "D5-M"
    assert projected["evidence_basis"]["discovery_regularized_training"] is True
    assert row["discovery_level"] == "D5-M"
    assert row["audit_status"] == "valid"
    assert discovery_map.pointer_value(summary, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(summary, row["control_pointer"]) is not None

    failed_records = deepcopy(_fixture_records())
    for record in failed_records:
        if record["arm"] == "DGT_full":
            record["classifier_shift_count"] = 0
            record["net_positive_signal"] = False
    failed = _project(failed_records)["summary_payload"]
    failed_row = discovery_map.discovery_row(spec, failed)
    assert failed_row["discovery_level"] == "DN"
    assert failed_row["failed_gate"] == "$.hardgate.gates.DRT-HG3.status"
    assert discovery_map.pointer_value(failed, failed_row["failed_gate"]) == "fail"


def test_current_lab_d5_m_projection_fails_closed_without_mechanism_dna_row():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    summary = _project()["summary_payload"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}

    projected = discovery_map.projection_payload(spec, summary, context)
    row = discovery_map.discovery_row(spec, summary, context)

    assert projected["verdict"] == "rejected"
    assert row["discovery_level"] == "DN"
    assert row["failed_gate"] == "$.training_mechanism_cert.status"


def test_drt_extension_forbidden_key_audit_rejects_host_env_and_terminal_verdict():
    audit = drt_extension_forbidden_key_audit(
        {
            "nested": {
                "host.env": "blocked",
                "value": ".refactor-loop/host.env",
                "cells": [{"terminal_verdict": "accepted"}],
            }
        }
    )

    assert audit["status"] == "fail"
    assert audit["hit_count"] >= 3


def test_drt_extension_hardgate_fail_demotes_discovery_map_row():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    summary = _project()["summary_payload"]
    gate_id = "DRT-EXT-HG2_uer_threshold"
    summary["drt_extension_hardgates"]["gates"][gate_id]["status"] = "fail"
    summary["drt_extension_hardgates"]["status"] = "fail"
    summary["drt_extension_hardgates"]["failed_gate"] = gate_id
    summary["drt_extension_hardgates"]["failed_gate_pointer"] = f"$.drt_extension_hardgates.gates.{gate_id}.status"

    row = discovery_map.discovery_row(spec, summary)
    projected = discovery_map.projection_payload(spec, summary)

    assert row["discovery_level"] == "DN"
    assert row["failed_gate"] == f"$.drt_extension_hardgates.gates.{gate_id}.status"
    assert discovery_map.pointer_value(summary, row["failed_gate"]) == "fail"
    assert projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "DN"


def test_drt_extension_pointers_resolve_inside_existing_drt_artifact():
    summary = _project()["summary_payload"]
    pointers = [
        summary["loss_family"]["owner_pointer"],
        summary["component_ablation"]["owner_pointer"],
        summary["training_method_comparison"]["owner_pointer"],
        summary["training_method_comparison"]["metric_pointers"]["uer"],
        summary["training_method_comparison"]["metric_pointers"]["uer_reduction"],
        f"{runner.JSON_ARTIFACT}:$.mechanism_ablation",
        *[row["evidence_pointer"] for row in summary["component_ablation"]["rows"]],
        *[row["quality_q_pointer"] for row in summary["component_ablation"]["rows"]],
        *[row["evidence_pointer"] for row in summary["loss_family"]["terms"].values()],
        *[
            pointer
            for row in summary["mechanism_ablation"]["comparisons"]
            for pointer in row["comparison_pointers"].values()
        ],
    ]

    unresolved = [
        pointer
        for pointer in pointers
        if pointer.startswith("reports/canonical/discovery-regularized-training.json:")
        and discovery_map.pointer_value(summary, pointer.split(":", 1)[1]) is None
    ]

    assert unresolved == []


def test_drt_extension_does_not_override_certificate_guided_dn_owner():
    training = canonical._specs_by_name()["certificate-guided-training"]
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]

    assert training.json_artifact == "reports/canonical/certificate-guided-training.json"
    assert discovery.json_artifact == "reports/canonical/certificate-guided-discovery.json"
    assert training.name == "certificate-guided-training"
    assert discovery.name == "certificate-guided-discovery"


def test_zero_row_and_dangling_torch_evidence_demote_to_dn():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    zero_row = runner.build_projection(generated_at="fixture-time", enable_torch=False)["summary_payload"]
    zero_projected = discovery_map.projection_payload(spec, zero_row)
    assert zero_projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "DN"
    assert zero_projected["main_verdict"]["discovery_regularized_training"]["status"] == "negative"

    dangling = _project()["summary_payload"]
    dangling["torch_training_evidence"]["protocols"] = []
    dangling["hardgate"]["gates"]["DRT-HG6"]["status"] = "pass"
    dangling["hardgate"]["status"] = "pass"
    dangling["hardgate"]["failed_gate"] = None
    dangling["discovery_map_signal"]["status"] = "d4-candidate"
    dangling["discovery_map_signal"]["level_candidate"] = "D4"
    dangling["discovery_map_signal"]["failed_gate"] = None
    dangling["discovery_map_signal"]["failed_gate_pointer"] = None
    projected = discovery_map.projection_payload(spec, dangling)
    assert projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "DN"
    assert projected["main_verdict"]["discovery_regularized_training"]["status"] == "negative"


def test_recursive_no_terminal_verdict_and_pointer_fields_resolve(tmp_path):
    projection = runner.build_projection(run_id="fixture-canonical", generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path)
    summary = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    capsule = json.loads((tmp_path / summary["run_artifacts"]["claim_capsule"]).read_text(encoding="utf-8"))

    assert "terminal_verdict" not in _recursive_keys({"summary": summary, "capsule": capsule})
    dangling = [
        (path, pointer)
        for path, pointer in _recursive_pointer_fields(summary)
        if isinstance(pointer, str)
        and pointer.startswith("$.")
        and discovery_map.pointer_value(summary, pointer) is None
    ]
    assert dangling == []
    assert summary["claim_capsule_ref"] == summary["run_artifacts"]["claim_capsule"]
    assert summary["not_claimed"] == capsule["not_claimed"]
    assert capsule["result_snapshot"]["quality_promotion_boundary"] == summary["quality_promotion_boundary"]
    assert (
        capsule["result_snapshot"]["quality_promotion_boundary"]["owner_pointer"]
        == "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary"
    )


def test_canonical_spec_uses_committed_config_and_source_artifacts():
    spec = canonical._specs_by_name()["discovery-regularized-training"]

    assert spec.command == ("python3", "scripts/run_discovery_regularized_training.py")
    assert "--cold" not in spec.command
    assert spec.json_artifact == runner.JSON_ARTIFACT
    assert "terminal_verdict" not in spec.required_json_keys
    assert "schema_id" in spec.required_json_keys
    assert "negative_witness_mutations" in spec.required_json_keys
    assert "training_loop_trace" in spec.required_json_keys
    assert "loss_family" in spec.required_json_keys
    assert "component_ablation" in spec.required_json_keys
    assert "training_method_comparison" in spec.required_json_keys
    assert "drt_extension_hardgates" in spec.required_json_keys
    assert "mechanism_ablation" in spec.required_json_keys
    assert "training_mechanism_cert" in spec.required_json_keys
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    assert ".refactor-loop/host.env" not in json.dumps(summary["source_artifacts"], sort_keys=True)
    assert "bedc_quality_lab/discovery_regularized_training.py" in summary["source_artifacts"]["producer_sources"]

import json
from copy import deepcopy
from pathlib import Path

import pytest

from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map


def _write_payload(root: Path, spec, payload):
    path = root / spec.json_artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _minimal_payload(spec):
    payload = {key: f"fixture-{key}" for key in spec.required_json_keys}
    if spec.name == "gap-head-on-h":
        payload.update({
            "treatment_verdict": {"positive": True},
            "control_protocol": {"same_budget_as_treatment": True},
            "control_verdict": {"positive": False},
        })
        return payload
    if spec.name == "gap-head-discovery":
        payload.update({
            "positive_discovery": True,
            "matched_random_control": {
                "control_verdict": {"positive": False},
                "control_projection": {"positive_discovery": True},
            },
        })
        return payload
    if spec.name == "gap-head-ablation":
        payload.update({"hardgate": {"status": "fail", "gates": {"learned_head": {"status": "pass"}}}})
        return payload
    if spec.name == "spectral-ablation-hinge":
        payload.update({
            "ledger_summary": {"status": "negative"},
            "negative_control_summary": {"treatment_better_than_all_controls": False},
        })
        return payload
    if spec.name == "certificate-guided-training":
        payload.update({
            "result": {"status": "negative"},
            "deltas": {"after_minus_before": {"debt_delta": -0.25}},
            "claim_gate": {"audit_improvement_tradeoff": True},
        })
        return payload
    if spec.name == "certificate-guided-discovery":
        payload.update({
            "main_claim_status": "observed-negative",
            "positive_discovery": False,
            "verdicts": [{"deltas": {"debt_delta": -0.25}}],
            "claim_gate": {"training_audit_improvement_tradeoff": True},
        })
        return payload
    if spec.name == "anisotropic-ou-sweep":
        payload.update({"transition_debt_by_grid": {"cell": {"status": "open-or-partial"}}})
        return payload
    if spec.name == "nongaussian-distribution-sweep":
        payload.update({
            "negative_result_ledger": [{"status": "negative"}],
            "coverage_item": {"debt_item": {"status": "open"}},
        })
        return payload
    if spec.name == "mixing-family-sweep":
        payload.update({"coverage_item": {"debt_item": {"status": "open"}}})
        return payload
    return payload


def _write_all_payloads(root: Path):
    for spec in canonical.CANONICAL_REPORTS:
        _write_payload(root, spec, _minimal_payload(spec))


def _write_json_artifact(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _read_json_artifact(root: Path, artifact: str):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _robustness_context_payload():
    return {
        "final_status": "pass",
        "acceptance_gates": {"status": "pass"},
        "A1_threshold_sweep": {"treatment_verdict": {"positive": True}},
        "A2_feature_ablation": {"status": "complete"},
        "A3_seed_expansion": {"status": "complete", "final_verdict": "robust_positive"},
        "A4_distribution_transfer": {
            "status": "complete",
            "policy": "pointer_only_existing_transfer_surfaces_no_retraining",
        },
    }


def _negative_witnesses_context_payload(*, expected_kind_count=8):
    return {
        "status": "pointer-only",
        "expected_kind_count": expected_kind_count,
        "witnesses": [
            {"kind": f"witness-{index}", "terminal_verdict": "rejected", "discovery_level": "DN"}
            for index in range(expected_kind_count)
        ],
    }


def _auroc_cell(*, mean, ci95_low, ci95_high):
    return {
        "ci95_half_width": 0.01,
        "ci95_high": ci95_high,
        "ci95_low": ci95_low,
        "mean": mean,
        "n": 10,
        "std": 0.01,
    }


def _learned_auroc_pass_cell():
    return _auroc_cell(mean=0.82, ci95_low=0.81, ci95_high=0.83)


def _matched_random_auroc_pass_cell():
    return _auroc_cell(mean=0.46, ci95_low=0.42, ci95_high=0.49)


def _observed_debt_transfer_context_payload(*, transfer_metric=False):
    payload = {
        "artifact_id": "bedc-quality-lab:gap-head-observed-debt-transfer",
        "hardgate_evidence": {
            "HG-A1": {"status": "pass"},
            "HG-A2": {"status": "pass"},
            "HG-A3": {"status": "pass"},
            "HG-A4": {"status": "pass"},
            "HG-A5": {"status": "pass" if transfer_metric else "fail"},
        },
        "surfaces": [
            {
                "control_verdict": {"positive": False},
                "hardgates": {
                    "HG-A1": {
                        "learned_auroc": _learned_auroc_pass_cell(),
                        "matched_random_auroc": _matched_random_auroc_pass_cell(),
                        "status": "pass" if transfer_metric else "fail",
                    }
                },
                "verdict": {"status": "pass" if transfer_metric else "failed"},
            }
        ],
        "not_claimed": ["no claim outside the listed observed-debt transfer surfaces"],
    }
    if transfer_metric:
        payload["gap_head_on_h_observed_debt_transfer"] = {"status": "pass"}
    return payload


def _dimension_mismatch_payload(*, status="pass"):
    return {
        "artifact_id": "bedc-quality-lab:dimension-mismatch-debt-transfer",
        "status": "pointer-only",
        "control_protocol": {"control_arm": "matched_random_gap_head"},
        "dimension_mismatch_debt_transfer": {
            "status": status,
            "status_code": "scoped-d4-boundary" if status == "pass" else "failed-boundary",
            "reason": "fixture",
            "scope": "encoder_dim grid against producer reference latent dimension",
            "discovery_level": "D4" if status == "pass" else "DN",
        },
        "boundary_ledger": {"d5_shortcut": False},
        "hardgate_evidence": {
            "HG-B3": {
                "learned_auroc": _learned_auroc_pass_cell(),
                "matched_random_auroc": _matched_random_auroc_pass_cell(),
                "matched_random_positive": False,
                "status": "pass" if status == "pass" else "fail",
            }
        },
        "not_claimed": ["no claim outside the listed encoder_dim-grid debt-transfer surface"],
    }


def _write_gap_head_d5_context(root: Path, *, transfer_metric=False, witness_count=8):
    _write_json_artifact(root, discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT, _robustness_context_payload())
    _write_json_artifact(
        root,
        discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
        _negative_witnesses_context_payload(expected_kind_count=witness_count),
    )
    _write_json_artifact(
        root,
        discovery_map.OBSERVED_DEBT_ARTIFACT,
        _observed_debt_transfer_context_payload(transfer_metric=transfer_metric),
    )


def _rewrite_gap_head_d5_artifact(root: Path, artifact: str, mutate):
    payload = _read_json_artifact(root, artifact)
    mutate(payload)
    _write_json_artifact(root, artifact, payload)


def _without_key(key):
    def mutate(payload):
        payload.pop(key, None)

    return mutate


def _set_nested(path, value):
    def mutate(payload):
        target = payload
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value

    return mutate


def _pop_nested(path):
    def mutate(payload):
        target = payload
        for key in path[:-1]:
            target = target[key]
        target.pop(path[-1], None)

    return mutate


def _add_gate_breaking_witness(payload):
    mutated_witnesses = deepcopy(payload["witnesses"])
    mutated_witnesses[0]["terminal_verdict"] = "accepted"
    payload["witnesses"] = mutated_witnesses


def _row_by_report(payload):
    return {row["report"]: row for row in payload["rows"]}


def test_discovery_map_has_one_row_per_canonical_report(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert [row["report"] for row in payload["rows"]] == [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert payload["row_count"] == len(canonical.CANONICAL_REPORTS)
    assert all(row["discovery_level"] in discovery_map.DISCOVERY_LEVELS for row in payload["rows"])


def test_threshold_frontier_without_projection_remains_d0_source_insufficient(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-threshold-frontier"]

    assert row["discovery_level"] == "D0"
    assert row["projection_status"] == "source-insufficient"
    assert row["audit_status"] == "valid"
    assert row["audit_reason"] == ""


@pytest.mark.parametrize("report", ["gap-head-on-h", "gap-head-discovery"])
def test_d4_rows_have_resolvable_control_pointer(tmp_path, report):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D4"
    assert evidence.control_pointer
    assert discovery_map.pointer_value(payload, evidence.control_pointer) is not None


def test_gap_head_on_h_current_readiness_stays_d4_with_observed_debt_transfer_missing(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=False)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert row["robustness_pointer"] == (
        "reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive"
    )
    assert row["adversarial_pointer"] == "reports/canonical/discovery_negative_witnesses.json:$.witnesses"
    assert row["observed_debt_transfer_pointer"] == (
        "reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status"
    )
    assert row["d5_readiness"]["threshold"]["status"] == "pass"
    assert row["d5_readiness"]["ablation"]["status"] == "pass"
    assert row["d5_readiness"]["seed_expansion"]["status"] == "pass"
    assert row["d5_readiness"]["adversarial"]["status"] == "pass"
    assert row["d5_readiness"]["observed_debt_transfer"]["status"] == "missing"


def test_gap_head_on_h_projects_to_d5_when_all_readiness_pointers_pass(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D5"
    assert row["audit_status"] == "valid"
    assert {criterion["status"] for criterion in row["d5_readiness"].values()} == {"pass"}


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"surfaces": [], "not_claimed": ["no observed-debt overclaim"]}),
        _set_nested(("not_claimed",), ["stub"]),
        _pop_nested(("surfaces", 0, "control_verdict")),
        _set_nested(("surfaces", 0, "control_verdict", "positive"), True),
        _pop_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc")),
        _set_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc", "mean"), "0.82"),
        _pop_nested(("surfaces", 0, "hardgates", "HG-A1", "matched_random_auroc")),
        _set_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc", "ci95_low"), 0.49),
    ],
)
def test_gap_head_on_h_d5_readiness_rejects_malformed_transfer_artifact(tmp_path, mutate):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)
    _rewrite_gap_head_d5_artifact(tmp_path, discovery_map.OBSERVED_DEBT_ARTIFACT, mutate)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert row["d5_readiness"]["observed_debt_transfer"]["status"] == "missing"


@pytest.mark.parametrize(
    ("criterion", "artifact", "mutate", "expected_status"),
    [
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A1_threshold_sweep"),
            "missing",
        ),
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A1_threshold_sweep", "treatment_verdict", "positive"), False),
            "missing",
        ),
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A1_threshold_sweep", "treatment_verdict", "positive"), "incomplete"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A2_feature_ablation"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A2_feature_ablation", "status"), "failed"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A2_feature_ablation", "status"), "incomplete"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A3_seed_expansion"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A3_seed_expansion", "status"), "incomplete"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A3_seed_expansion", "final_verdict"), "failed"),
            "missing",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _without_key("witnesses"),
            "failed",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _set_nested(("expected_kind_count",), 7),
            "failed",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _add_gate_breaking_witness,
            "failed",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _without_key("gap_head_on_h_observed_debt_transfer"),
            "missing",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _set_nested(("gap_head_on_h_observed_debt_transfer", "status"), "failed"),
            "missing",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _set_nested(("gap_head_on_h_observed_debt_transfer", "status"), "incomplete"),
            "missing",
        ),
    ],
)
def test_gap_head_on_h_d5_readiness_fails_closed_per_real_criterion(
    tmp_path,
    criterion,
    artifact,
    mutate,
    expected_status,
):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)
    _rewrite_gap_head_d5_artifact(tmp_path, artifact, mutate)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    statuses = {name: value["status"] for name, value in row["d5_readiness"].items()}
    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert statuses[criterion] == expected_status
    assert {name for name, status in statuses.items() if status != "pass"} == {criterion}


def test_gap_head_on_h_d5_claim_with_unresolved_pointer_is_invalid(monkeypatch):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = _minimal_payload(spec)
    ledger = discovery_map.GapHeadD5ReadinessLedger(
        criteria=(
            discovery_map.GapHeadD5Criterion(
                name="threshold",
                status="pass",
                artifact=discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
                pointer="$.missing_positive_cell",
                reason="fixture",
            ),
        )
    )

    def fake_readiness(context):
        return ledger

    monkeypatch.setattr(discovery_map, "_gap_head_d5_readiness", fake_readiness)

    row = discovery_map.discovery_row(
        spec,
        payload,
        {discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT: {"final_status": "pass"}},
    )

    assert row["discovery_level"] == "D5"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-d5-pointer-threshold"


def test_adversarial_witness_count_does_not_create_positive_discovery(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True, witness_count=8)
    spec = canonical._specs_by_name()["gap-head-on-h"]
    _write_payload(
        tmp_path,
        spec,
        {
            "treatment_verdict": {"positive": False},
            "control_protocol": {"same_budget_as_treatment": True},
            "control_verdict": {"positive": False},
        },
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["d5_readiness"]["adversarial"]["status"] == "pass"
    assert row["discovery_level"] == "D0"
    assert row["classifier_reasons"] == ["no classifier shift or debt improvement"]


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("certificate-guided-training", "$.result.status"),
        ("certificate-guided-discovery", "$.positive_discovery"),
        ("gap-head-ablation", "$.hardgate.status"),
        ("spectral-ablation-hinge", "$.negative_control_summary.treatment_better_than_all_controls"),
    ],
)
def test_dn_rows_have_failed_gate_pointing_to_negative_cell(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "DN"
    assert evidence.failed_gate == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("mixing-family-sweep", "$.coverage_item.debt_item"),
        ("anisotropic-ou-sweep", "$.transition_debt_by_grid"),
        ("nongaussian-distribution-sweep", "$.negative_result_ledger"),
    ],
)
def test_d1_rows_have_debt_row_pointer_to_real_evidence(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D1"
    assert evidence.debt_row_pointer == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


def test_run_reports_index_contains_discovery_map(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        _write_payload(tmp_path, spec, _minimal_payload(spec))
        markdown = tmp_path / spec.markdown_artifact
        markdown.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert (tmp_path / "reports" / "canonical" / "discovery_map.json").exists()
    assert (tmp_path / "reports" / "canonical" / "discovery_map.md").exists()


def test_strict_manifest_audit_marks_missing_control_invalid(tmp_path):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = {"treatment_verdict": {"positive": True}, "control_verdict": {"positive": False}}
    row = discovery_map.discovery_row(spec, payload)

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-control-pointer"

    _write_all_payloads(tmp_path)
    _write_payload(tmp_path, spec, payload)
    discovery_map.write_discovery_map(root=tmp_path, generated_at="fixture-time")
    with pytest.raises(SystemExit):
        old_root = discovery_map.ROOT
        try:
            discovery_map.ROOT = tmp_path
            discovery_map.main(["--strict-manifest-audit"])
        finally:
            discovery_map.ROOT = old_root


def test_manifest_audit_reports_unregistered_json_and_strict_fails(tmp_path):
    _write_all_payloads(tmp_path)
    unregistered = tmp_path / "reports" / "canonical" / "unregistered-extra.json"
    unregistered.write_text(json.dumps({"schema_id": "fixture"}) + "\n", encoding="utf-8")

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert payload["manifest_audit"]["unregistered_json_artifacts"] == [
        "reports/canonical/unregistered-extra.json",
    ]

    old_root = discovery_map.ROOT
    try:
        discovery_map.ROOT = tmp_path
        with pytest.raises(SystemExit) as excinfo:
            discovery_map.main(["--strict-manifest-audit"])
    finally:
        discovery_map.ROOT = old_root

    assert excinfo.value.code == 1


def test_manifest_audit_registers_formal_hardening_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    formal = tmp_path / "reports" / "canonical" / "formal_hardening.json"
    formal.write_text(
        json.dumps(
            {
                "artifact_id": "bedc-quality-lab:formal-hardening",
                "ready": False,
                "verification_ledger": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert "reports/canonical/formal_hardening.json" not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_manifest_audit_registers_observed_debt_transfer_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.OBSERVED_DEBT_ARTIFACT,
        {
            "artifact_id": "bedc-quality-lab:gap-head-observed-debt-transfer",
            "gap_head_on_h_observed_debt_transfer": {"status": "failed"},
            "surfaces": [{"verdict": {"status": "failed"}}],
            "hardgate_evidence": {"HG-A5": {"status": "fail"}},
            "not_claimed": ["fixture"],
        },
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert discovery_map.OBSERVED_DEBT_ARTIFACT not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_manifest_audit_registers_dimension_mismatch_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="failed"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_dimension_mismatch_pass_projects_only_scoped_d4_no_d5_shortcut(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="pass"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["dimension-mismatch-debt-transfer"]

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert row["control_pointer"] == "$.control_protocol"
    assert "d5_readiness" not in row


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"hardgate_evidence": {}, "not_claimed": ["no dimension-mismatch overclaim"]}),
        _set_nested(("not_claimed",), ["stub"]),
        _pop_nested(("hardgate_evidence", "HG-B3", "matched_random_auroc")),
        _set_nested(("hardgate_evidence", "HG-B3", "matched_random_positive"), True),
        _set_nested(("hardgate_evidence", "HG-B3", "learned_auroc", "ci95_low"), 0.49),
    ],
)
def test_dimension_mismatch_pass_rejects_malformed_transfer_artifact(tmp_path, mutate):
    _write_all_payloads(tmp_path)
    payload = _dimension_mismatch_payload(status="pass")
    mutate(payload)
    _write_json_artifact(tmp_path, discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["dimension-mismatch-debt-transfer"]

    assert row["projection_status"] == "source-insufficient"
    assert row["evidence_pointer"] == discovery_map.DIMENSION_MISMATCH_TRANSFER_POINTER
    assert "control_pointer" not in row
    assert row["discovery_level"] != "D4"
    assert row["audit_status"] == "valid"


def test_dimension_mismatch_failed_projects_dn_with_failed_gate(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="failed"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["dimension-mismatch-debt-transfer"]

    assert row["discovery_level"] == "DN"
    assert row["audit_status"] == "valid"
    assert row["failed_gate"] == "$.dimension_mismatch_debt_transfer.status"

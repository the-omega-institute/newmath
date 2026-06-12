import json
from copy import deepcopy
import ast
import inspect
import textwrap

import pytest

import scripts.run_dgt_l0_controls as runner
from bedc_quality_lab import dgt_l0_controls
from bedc_quality_lab.dgt_l0_controls import (
    CANONICAL_JSON_ARTIFACT,
    CONTROL_POINTERS,
    rebuild_l0_projection,
    validate_payload,
)


def _payload():
    return dgt_l0_controls.build_payload(generated_at="fixture-time", requested_device="cpu")


def _first_seed_witness_rows(payload):
    records = payload["_raw_records"]
    first_seed = dgt_l0_controls.REPLAY_SEEDS[0]
    return {row["arm_id"]: deepcopy(row) for row in records if row["seed"] == first_seed}


def _witness_hit_counts(payload):
    return {
        row["witness"]: row["hit_count"]
        for row in payload["negative_witness_sweep"]["witness_rows"]
    }


def _sweep_hit_counts(dgt_row, base_row, matched_row):
    return {
        row["witness"]: row["hit_count"]
        for row in dgt_l0_controls._negative_witness_sweep(dgt_row, base_row, matched_row)["witness_rows"]
    }


def benefit_debt_tradeoff():
    payload = _payload()
    rows = _first_seed_witness_rows(payload)

    assert _witness_hit_counts(payload)["benefit_debt_tradeoff"] == 0

    rows["DGT_full"]["metrics"]["benefit_q"] = rows["DGT_full"]["metrics"]["debt_q"]
    hits = _sweep_hit_counts(
        rows["DGT_full"],
        rows["base_transformer_l0"],
        rows["matched_random_structural_control"],
    )

    assert hits["benefit_debt_tradeoff"] == 1


def single_threshold_escape():
    payload = _payload()
    rows = _first_seed_witness_rows(payload)

    assert _witness_hit_counts(payload)["single_threshold_escape"] == 0

    rows["DGT_full"]["metrics"]["quality_q"] = rows["base_transformer_l0"]["metrics"]["quality_q"]
    hits = _sweep_hit_counts(
        rows["DGT_full"],
        rows["base_transformer_l0"],
        rows["matched_random_structural_control"],
    )

    assert hits["single_threshold_escape"] == 1


def control_positive():
    payload = _payload()
    rows = _first_seed_witness_rows(payload)

    assert _witness_hit_counts(payload)["control_positive"] == 0

    rows["base_transformer_l0"]["metrics"]["quality_q"] = rows["DGT_full"]["metrics"]["quality_q"]
    sweep = dgt_l0_controls._negative_witness_sweep(
        rows["DGT_full"],
        rows["base_transformer_l0"],
        rows["matched_random_structural_control"],
    )
    hits = {row["witness"]: row["hit_count"] for row in sweep["witness_rows"]}

    assert hits["control_positive"] == 1
    assert sweep["critical_hit_count"] == 1
    assert sweep["status"] == "fail"


def matched_random_positive():
    payload = _payload()
    rows = _first_seed_witness_rows(payload)

    assert _witness_hit_counts(payload)["matched_random_positive"] == 0

    rows["matched_random_structural_control"]["metrics"]["uer_reduction"] = rows["DGT_full"]["metrics"]["uer_reduction"]
    sweep = dgt_l0_controls._negative_witness_sweep(
        rows["DGT_full"],
        rows["base_transformer_l0"],
        rows["matched_random_structural_control"],
    )
    hits = {row["witness"]: row["hit_count"] for row in sweep["witness_rows"]}

    assert hits["matched_random_positive"] == 1
    assert sweep["critical_hit_count"] == 1
    assert sweep["status"] == "fail"


benefit_debt_tradeoff.__test__ = True
single_threshold_escape.__test__ = True
control_positive.__test__ = True
matched_random_positive.__test__ = True


def test_dgt_l0_controls_true_training_payload_is_ready():
    payload = _payload()

    assert payload["schema_id"] == "bedc-quality-lab:dgt-l0-controls"
    assert payload["artifact_id"] == "bedc-quality-lab:dgt-l0-controls"
    assert payload["l0_toy_projection"]["review_status"] == "scoped-boundary"
    assert payload["honest_metric_review"]["status"] == "scoped-boundary"
    assert payload["feature_audit"]["status"] == "pass"
    assert payload["l0_toy_projection"]["ladder_consumption"]["status"] == "scoped-boundary"
    assert payload["l0_toy_projection"]["ref_pointers"] == CONTROL_POINTERS
    assert payload["construct_validity_hardgates"]["status"] == "fail"
    assert payload["construct_validity_hardgates"]["failed_gates"] == ["CV-HG4"]
    assert payload["construct_validity_hardgates"]["gates"]["CV-HG4"]["status"] == "fail"
    assert payload["construct_validity_hardgates"]["evidence"]["hand_feature_ledger"] == {
        "mode": "candidate-only-ledger",
        "shared_across_arms": False,
        "features": ["target_signal", "surface_suite"],
        "candidate_only_features": list(dgt_l0_controls.DGT_CANDIDATE_ONLY_FEATURES),
    }
    assert payload["controls"]["base_transformer_control"]["loss_decrease"] > 0
    assert payload["controls"]["base_transformer_control"]["parameter_l2_delta"] > 0
    assert payload["controls"]["matched_random_structural_control"]["classifier_shift_count"] is None
    assert payload["compute_param_ledger"]["compute_units"] > 0
    assert payload["compute_param_ledger"]["parameter_count"] > 0
    assert payload["negative_witness_sweep"]["critical_hit_count"] == 0
    assert payload["negative_witness_sweep"]["required_witnesses"] == list(dgt_l0_controls.REQUIRED_WITNESSES)
    assert {row["witness"] for row in payload["negative_witness_sweep"]["boundary_ledger"]} == {
        "score_margin_shortcut",
        "scale_leakage",
        "forbidden_inference_column",
        "scope_expansion",
        "stale_projection",
    }
    assert all(row["regression_test_pointer_resolves"] for row in payload["negative_witness_sweep"]["witness_rows"])
    assert payload["independent_replay"]["comparisons"]["dgt_quality_ci_low_gt_base"] is True
    assert payload["independent_replay"]["comparisons"]["dgt_uer_reduction_gt_matched_random"] is True


def test_dgt_l0_controls_owns_l0_review_status_and_pass_hardgates():
    payload = _payload()
    projection = payload["l0_toy_projection"]
    pass_gates = projection["hardgate_statuses"]["pass"]["gates"]

    assert projection["review_status"] == "scoped-boundary"
    assert tuple(pass_gates) == tuple(f"L0-PASS-HG{index}" for index in range(1, 7))
    assert all(row["status"] == "pass" for row in pass_gates.values())
    assert projection["honest_metric_review_ref"] == {
        "artifact": CANONICAL_JSON_ARTIFACT,
        "pointer": "$.honest_metric_review",
    }
    assert projection["evidence_refs"] == {
        key: CONTROL_POINTERS[key]
        for key in (
            "base_transformer_control",
            "matched_random_structural_control",
            "compute_param_ledger",
            "negative_witness_sweep",
            "independent_replay",
        )
    }
    serialized = json.dumps({key: value for key, value in payload.items() if key != "l0_toy_projection"}, sort_keys=True)
    assert "L0-PASS-HG" not in serialized
    assert '"review_status"' not in serialized


@pytest.mark.parametrize("witness_test", [benefit_debt_tradeoff, single_threshold_escape, control_positive, matched_random_positive])
def test_dgt_l0_controls_negative_witness_pointer_targets_are_assertive(witness_test):
    witness_test()


def test_dgt_l0_controls_negative_witness_pointer_resolution_fails_closed(monkeypatch):
    payload = _payload()

    monkeypatch.setattr(dgt_l0_controls, "_regression_test_pointer_resolves", lambda pointer: False)
    payload["negative_witness_sweep"] = dgt_l0_controls._negative_witness_sweep(
        _first_seed_witness_rows(payload)["DGT_full"],
        _first_seed_witness_rows(payload)["base_transformer_l0"],
        _first_seed_witness_rows(payload)["matched_random_structural_control"],
    )
    payload["l0_toy_projection"] = rebuild_l0_projection(payload)

    assert payload["negative_witness_sweep"]["status"] == "fail"
    assert payload["negative_witness_sweep"]["pass_cells"]["regression_test_pointers_resolve"] is False
    assert payload["l0_toy_projection"]["hardgate_statuses"]["negative_witness"]["gates"]["NW-L0-HG5"]["status"] == "fail"
    assert payload["l0_toy_projection"]["review_status"] == "blocked"


@pytest.mark.parametrize("failure_mode", ["torch_unavailable", "training_failed"])
def test_dgt_l0_controls_unavailable_payload_validates_blocked(monkeypatch, failure_mode):
    if failure_mode == "torch_unavailable":
        real_import_module = dgt_l0_controls.importlib.import_module

        def unavailable_import(name):
            if name == "torch":
                raise ModuleNotFoundError("torch hidden for fail-closed test")
            return real_import_module(name)

        monkeypatch.setattr(dgt_l0_controls.importlib, "import_module", unavailable_import)
    else:
        def failing_train_arm(*_args, **_kwargs):
            raise RuntimeError("training failed for fail-closed test")

        monkeypatch.setattr(dgt_l0_controls, "_train_arm", failing_train_arm)

    payload = dgt_l0_controls.build_payload(generated_at="fixture-time", requested_device="cpu")
    projection = payload["l0_toy_projection"]

    validate_payload(payload)
    assert projection["review_status"] == "blocked"
    assert projection["status"] == "fail"
    assert payload["compute_param_ledger"]["status"] == "fail"
    assert payload["construct_validity_hardgates"]["status"] == "fail"
    assert set(payload["construct_validity_hardgates"]["failed_gates"]) == {"CV-HG3", "CV-HG4", "CV-HG5"}
    assert projection["hardgate_statuses"]["ledger"]["gates"]["LEDGER-L0-HG1"]["status"] == "fail"
    assert projection["hardgate_statuses"]["L0"]["gates"]["L0-HG3"]["status"] == "fail"
    assert projection["hardgate_statuses"]["pass"]["status"] == "fail"


def test_dgt_l0_controls_rejects_unavailable_construct_validity_stub_pass():
    payload = dgt_l0_controls.unavailable_payload(
        generated_at="fixture-time",
        requested_device="cpu",
        reason="torch unavailable",
    )
    payload["construct_validity_hardgates"] = dgt_l0_controls.construct_validity_projection(
        dgt_l0_controls.ConstructValidityEvidence(
            task_variables={"variables": ["x0"]},
            label_variables={"variables": ["toy_binary_label"]},
            arm_input_access={
                "label_invisibility_certificate": True,
                "arms": {"candidate": {"variables": ["x0"]}, "control": {"variables": ["x0"]}},
            },
            arm_roles={"candidate": "candidate", "controls": ["control"]},
            finite_table={"coverage_status": "bounded-control", "support_count": 1, "rule_abstraction_claim": False},
            hand_feature_ledger={"mode": "no-gate", "features": [], "candidate_only_features": []},
            metric_source={"source_kind": "training-evaluation", "metric_keys": ["quality_q"]},
        ),
        artifact=dgt_l0_controls.CANONICAL_JSON_ARTIFACT,
        pointer="$.construct_validity_hardgates",
    )

    with pytest.raises(ValueError, match="without training records"):
        validate_payload(payload)


def test_dgt_l0_controls_writes_run_local_artifacts_without_report_fingerprint_authority(tmp_path):
    payload = _payload()
    dgt_l0_controls.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")

    canonical_payload = json.loads((tmp_path / CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_capsule = json.loads(
        (tmp_path / "reports/runs/discovery-gated-transformer/l0-toy-controls/claim_capsule.json").read_text(
            encoding="utf-8"
        )
    )

    assert canonical_payload["l0_toy_projection"]["review_status"] == "scoped-boundary"
    assert claim_capsule["owner_artifact"] == CANONICAL_JSON_ARTIFACT
    assert claim_capsule["owner_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.l0_toy_projection"
    assert not (tmp_path / "reports/canonical/dgt-l0-controls.fingerprint.json").exists()


def test_dgt_l0_controls_cli_main_writes_cpu_artifact_layout(tmp_path, capsys):
    exit_code = runner.main(["--root", str(tmp_path), "--generated-at", "fixture", "--requested-device", "cpu"])

    assert exit_code == 0
    summary = json.loads(capsys.readouterr().out)
    assert summary["artifact_id"] == dgt_l0_controls.ARTIFACT_ID
    assert summary["status"] == "scoped-boundary"
    assert summary["review_status"] == "scoped-boundary"
    assert summary["device"] == "cpu"
    assert summary["compute_units"] > 0

    run_artifacts = dgt_l0_controls.run_artifacts_payload()
    expected_artifacts = [
        dgt_l0_controls.CANONICAL_JSON_ARTIFACT,
        dgt_l0_controls.CANONICAL_MARKDOWN_ARTIFACT,
        run_artifacts["summary"],
        run_artifacts["raw_metrics"],
        run_artifacts["claim_capsule"],
        run_artifacts["report"],
    ]
    assert all((tmp_path / artifact).exists() for artifact in expected_artifacts)


@pytest.mark.parametrize(
    ("group", "mutate", "expected_gate"),
    [
        ("L0", lambda payload: payload["controls"]["base_transformer_control"].update({"status": "fail"}), "L0-HG1"),
        ("base", lambda payload: payload["controls"]["base_transformer_control"].update({"loss_decrease": 0.0}), "BASE-L0-HG4"),
        (
            "matched_random",
            lambda payload: payload["honest_metric_review"].update({"boundary_rows": []}),
            "MR-L0-HG6",
        ),
        ("ledger", lambda payload: payload["compute_param_ledger"].update({"compute_units": 0}), "LEDGER-L0-HG4"),
        ("negative_witness", lambda payload: payload["negative_witness_sweep"].update({"critical_hit_count": 1}), "NW-L0-HG3"),
        (
            "replay",
            lambda payload: payload["independent_replay"]["comparisons"].update({"dgt_quality_ci_low_gt_base": False}),
            "REPLAY-L0-HG4",
        ),
        (
            "pointer",
            lambda payload: payload["l0_toy_projection"]["ref_pointers"]["base_transformer_control"].update(
                {"pointer": "$.missing"}
            ),
            "PTR-HG1",
        ),
    ],
)
def test_dgt_l0_controls_each_gate_group_fails_closed(group, mutate, expected_gate):
    payload = _payload()
    mutate(payload)
    payload["l0_toy_projection"] = rebuild_l0_projection(payload)

    assert payload["l0_toy_projection"]["review_status"] == "blocked"
    assert payload["l0_toy_projection"]["hardgate_statuses"][group]["gates"][expected_gate]["status"] == "fail"
    assert f"{group}:{expected_gate}" in payload["l0_toy_projection"]["failure_reasons"]


def test_dgt_l0_controls_projection_pointer_fails_closed():
    payload = _payload()
    payload["l0_toy_projection"]["ref_pointers"]["l0_control_projection"]["pointer"] = "$.missing"
    payload["l0_toy_projection"] = rebuild_l0_projection(payload)

    pointer_gates = payload["l0_toy_projection"]["hardgate_statuses"]["pointer"]["gates"]

    assert tuple(pointer_gates) == tuple(f"PTR-HG{index}" for index in range(1, len(CONTROL_POINTERS) + 1))
    assert len(pointer_gates) == len(CONTROL_POINTERS) == 6
    assert pointer_gates["PTR-HG6"]["status"] == "fail"
    assert payload["l0_toy_projection"]["hardgate_statuses"]["pass"]["gates"]["L0-PASS-HG6"]["status"] == "fail"
    assert payload["l0_toy_projection"]["review_status"] == "blocked"
    assert "pointer:PTR-HG6" in payload["l0_toy_projection"]["failure_reasons"]
    assert "pass:L0-PASS-HG6" in payload["l0_toy_projection"]["failure_reasons"]


def test_dgt_l0_controls_rejects_stale_projection_after_mutation():
    payload = _payload()
    payload["compute_param_ledger"]["parameter_count"] = 0

    with pytest.raises(ValueError, match="hardgate evaluation|positive compute"):
        validate_payload(payload)


def test_metric_signature_excludes_arm_spec():
    signature = str(inspect.signature(dgt_l0_controls.L0HonestMetric.evaluate))
    source = textwrap.dedent(inspect.getsource(dgt_l0_controls.L0HonestMetric.evaluate))
    tree = ast.parse(source)
    names = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
    attributes = {node.attr for node in ast.walk(tree) if isinstance(node, ast.Attribute)}

    for forbidden in ("L0ArmSpec", "arm_id", "feature_mode", "quality_bonus", "uer_penalty"):
        assert forbidden not in signature
        assert forbidden not in source
        assert forbidden not in names
        assert forbidden not in attributes


def test_arm_label_permutation_invariance():
    payload = _payload()
    outcomes = [row["measured_outcome"] for row in payload["_raw_records"]]
    permuted = []
    label_map = {
        "DGT_full": "candidate-renamed",
        "base_transformer_l0": "base-renamed",
        "matched_random_structural_control": "matched-renamed",
    }
    for row in outcomes:
        copied = dict(row)
        copied["arm_label"] = label_map.get(copied["arm_label"], copied["arm_label"])
        permuted.append(copied)

    original = dgt_l0_controls.L0HonestMetric().evaluate(outcomes, thresholds={})
    relabeled = dgt_l0_controls.L0HonestMetric().evaluate(
        permuted,
        thresholds={
            "arm_labels": [
                "candidate-renamed",
                "base-renamed",
                "matched-renamed",
                "parameter_matched_transformer",
                "compute_matched_transformer",
            ],
            "candidate_label": "candidate-renamed",
            "base_label": "base-renamed",
            "matched_label": "matched-renamed",
        },
    )

    assert original["quality_q"] == relabeled["quality_q"]
    assert original["UER"] == relabeled["UER"]
    assert original["uer_reduction"] == relabeled["uer_reduction"]
    assert original["hardgate_rows"] == relabeled["hardgate_rows"]


def test_feature_audit_demotes_dgt_only_target_signal():
    audit = dgt_l0_controls._measured_feature_audit(
        arm_label="DGT_full",
        feature_columns=["x", "x0_times_x1", "x2_minus_x3", "abs(target_signal)"],
        shared_feature_columns=["x", "x0_times_x1", "x2_minus_x3"],
        declared_shared_across_controls=False,
    )
    outcome = dgt_l0_controls.MeasuredL0Outcome(
        arm_label="DGT_full",
        seed=1,
        split_id="eval",
        task_accuracy=1.0,
        margin=0.5,
        unlogged_error_count=0,
        logged_false_alarm_count=0,
        eval_count=10,
        measured_feature_audit=audit,
    )

    review = dgt_l0_controls.L0HonestMetric().evaluate([outcome], thresholds={})

    assert review["feature_audit"]["status"] == "fail"
    assert "abs(target_signal)" in review["feature_audit"]["dgt_only_forbidden_hits"]
    assert review["status"] == "blocked"


def test_shared_declared_feature_requires_control_parity():
    failed = dgt_l0_controls.evaluate_feature_declaration(
        ["x", "target_signal"],
        [["x"], ["x", "random_projection"]],
    )
    passed = dgt_l0_controls.evaluate_feature_declaration(
        ["x", "target_signal"],
        [["x", "target_signal"], ["x", "target_signal"]],
    )

    assert failed["status"] == "fail"
    assert passed["status"] == "pass"


def test_measured_owner_required_for_unmeasurable_cells():
    payload = _payload()

    assert payload["honest_metric_review"]["classifier_shift_count"] is None
    assert any(row["status"] == "measured-owner-required" for row in payload["boundary_ledger"])
    assert payload["honest_metric_review"]["hardgate_rows"]["L0-METRIC-HG5"]["status"] == "pass"


def test_injected_prior_only_negative_boundary():
    payload = _payload()
    public = {key: value for key, value in payload.items() if key != "_raw_records"}
    allowed = json.dumps(public["negative_evidence"], sort_keys=True)
    forbidden_surfaces = json.dumps(
        {
            "honest_metric_review": public["honest_metric_review"],
            "l0_toy_projection": public["l0_toy_projection"],
            "ladder_consumption": public["ladder_consumption"],
        },
        sort_keys=True,
    )

    assert "prior_injected_metric_result" in allowed
    assert "prior_injected_metric_result" not in forbidden_surfaces

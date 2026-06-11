import json
import inspect

import pytest

from bedc_quality_lab import dgt_neural_ablation as owner
from scripts import run_dgt_neural_ablation as runner


def _summary(metrics_by_seed):
    return {"metrics_by_seed": {str(seed): dict(metrics) for seed, metrics in metrics_by_seed.items()}}


def _metric_row(*, step, seed, arm="full_DGT", hits=0):
    metrics = {metric: 0.0 for metric in owner.METRIC_KEYS}
    metrics.update(
        {
            "quality_q": 0.5,
            "benefit_q": 0.5,
            "scope_pressure_q": 0.5,
            "JetCoverage": 0.5,
            "compute_cost": 0.01,
        }
    )
    return {
        "train_steps": step,
        "seed": seed,
        "arm_id": arm,
        "task_id": "scope_boundary_pressure",
        "device": "cpu",
        "optimizer_steps": step,
        "compute_units": 0.01,
        "parameter_count": 12,
        "wall_time_proxy": 0.001,
        "negative_witness_hits": hits,
        "metrics": metrics,
    }


def _matrix_with_component(component, delta, step=128):
    zero = owner.paired_delta(
        _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)}),
        _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)}),
        paired_ci_min_seeds=8,
    )
    matrix = {}
    for item in owner.COMPONENTS:
        selected = delta if item == component else zero
        matrix[f"DGT_without_{item}"] = {**selected, "by_steps": {str(step): selected}}
    return matrix


def _payload_with_synthetic_claim():
    payload = owner.build_payload(
        generated_at="fixture",
        requested_device="cpu",
        run_spec=owner.DgtNeuralAblationRunSpec.quick_test(),
    )
    mutated = json.loads(json.dumps(payload))
    claim = {
        "component": "LAT",
        "claim_status": "allowed",
        "claim_scope": "bounded toy training",
        "evidence_scope": list(owner.COMPONENT_CAUSAL_EVIDENCE_SCOPE),
        "claim_text": "Under the bounded toy training protocol, removing LAT has measured degradation.",
        "stable_step_settings": [8],
        "ci_low_metrics": {"quality_q": 0.02},
        "metric_delta_pointer": f"{owner.CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_LAT",
        "record_pointer": f"{owner.CANONICAL_JSON_ARTIFACT}:$.records",
        "terminal_verdict_scope": "Core",
        "paired_seed_count": 2,
        "confidence_interval_pointer": f"{owner.CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_LAT.by_steps",
    }
    mutated["stable_component_causal_claims"] = [claim]
    mutated["stable_causal_attribution"] = "partial"
    mutated["component_causal_claims"] = [claim]
    mutated["boundary_ledger"] = [
        {**row, "status": "measured", "reason": "paired cross-seed CI-low supports a scoped component-causal claim", "claim_blocked": False}
        if row["component"] == "LAT"
        else row
        for row in mutated["boundary_ledger"]
    ]
    mutated["stable_boundary_ledger"] = mutated["boundary_ledger"]
    mutated["forbidden_claim_term_audit"] = owner._forbidden_claim_term_audit({"claims": mutated["component_causal_claims"]})
    mutated["training_protocol"]["status"] = "available"
    for gate in mutated["pure_hardgates"]["gates"].values():
        gate["status"] = "pass"
    mutated["pure_hardgates"]["status"] = "pass"
    mutated["pure_hardgates"]["failed_gate"] = None
    for gate in mutated["nabl_hardgates"]["gates"].values():
        gate["status"] = "pass"
    mutated["nabl_hardgates"]["status"] = "pass"
    mutated["nabl_hardgates"]["failed_gate"] = None
    for gate in mutated["nabl2_hardgates"]["gates"].values():
        gate["status"] = "pass"
    mutated["nabl2_hardgates"]["status"] = "pass"
    mutated["nabl2_hardgates"]["failed_gate"] = None
    return mutated


def test_registry_has_exact_arms_and_metrics():
    run_spec = owner.DgtNeuralAblationRunSpec.quick_test()
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)

    assert tuple(payload["module_registry"]) == owner.ARM_IDS
    assert len(payload["records"]) == len(owner.ARM_IDS) * run_spec.seed_count * len(run_spec.step_grid) * len(owner.TASK_IDS)
    assert sorted({row["arm_id"] for row in payload["records"]}, key=list(owner.ARM_IDS).index) == list(owner.ARM_IDS)
    for row in payload["records"]:
        assert set(row["metrics"]) == set(owner.METRIC_KEYS)
        assert set(owner.OUTCOME_FIELDS) <= set(row)
        assert row["requested_training_backend"] == "torch"
        assert row["train_steps"] in run_spec.step_grid
        assert row["optimizer_steps"] == row["train_steps"]
        assert row["compute_units"] > 0.0
        assert row["parameter_count"] > 0
        assert row["wall_time_proxy"] > 0.0
        assert row["gradient_update_steps"] > 0
        assert row["parameter_delta_l2"] > 0.0
        outcome = owner.TrainingOutcome(**{field: row[field] for field in owner.OUTCOME_FIELDS})
        assert owner.derive_training_metrics(outcome)["metrics"] == row["metrics"]


def test_run_spec_defaults_use_robust_grid():
    run_spec = owner.DgtNeuralAblationRunSpec.canonical()

    assert run_spec.step_grid == (128, 256)
    assert run_spec.seed_count == 8
    assert len(run_spec.arms) == 11
    assert run_spec.paired_ci_min_seeds == 8


def test_paired_ci_fails_closed_below_eight_seeds():
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(7)})
    ablated = _summary({seed: {metric: 0.4 for metric in owner.METRIC_KEYS} for seed in range(7)})

    delta = owner.paired_delta(full, ablated, paired_ci_min_seeds=8)

    assert delta["status"] == "fail"
    assert delta["failed_gate"] == "NABL2-HG1"


def test_allowed_claim_requires_ci_low_above_threshold():
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} | {"quality_q": 0.7} for seed in range(8)})
    ablated = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} | {"quality_q": 0.6} for seed in range(8)})
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128,),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)

    delta = owner.paired_delta(full, ablated, paired_ci_min_seeds=8)
    by_steps = projection._robustness_by_steps(_matrix_with_component("LAT", delta))

    assert by_steps["128"]["components"]["LAT"]["status"] == "allowed"
    assert by_steps["128"]["components"]["LAT"]["positive_ci_low_metrics"]["quality_q"] > owner.MEASURABLE_EFFECT_THRESHOLD


def test_no_effect_component_stays_blocked_across_seed_grid():
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)})
    ablated = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)})
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128,),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)

    delta = owner.paired_delta(full, ablated, paired_ci_min_seeds=8)
    by_steps = projection._robustness_by_steps(_matrix_with_component("LAT", delta))
    boundary = projection._stable_boundary_ledger(by_steps, [])

    assert by_steps["128"]["components"]["LAT"]["status"] == "blocked"
    assert [row for row in boundary if row["component"] == "LAT"][0]["reason"] == "NABL2-HG3"


def test_nabl2_hg2_passes_vacuously_without_allowed_claims():
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128,),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)
    rows = [row for step in run_spec.step_grid for seed in run_spec.seed_list for arm in run_spec.arms for row in [_metric_row(step=step, seed=seed, arm=arm)]]
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)})
    delta = owner.paired_delta(full, full, paired_ci_min_seeds=8)
    by_steps = projection._robustness_by_steps(_matrix_with_component("LAT", delta))
    boundary = projection._stable_boundary_ledger(by_steps, [])
    hardgates = projection._nabl2_hardgates(
        rows=rows,
        robustness_by_steps=by_steps,
        claims=[],
        boundary=boundary,
        compute_ledger=projection._compute_ledger(rows),
        source_audit={"status": "pass"},
        negative_witness_sweep={"status": "pass"},
    )

    assert hardgates["gates"]["NABL2-HG2"]["status"] == "pass"
    assert hardgates["status"] == "pass"


def test_stable_null_causal_attribution_is_loud_and_keeps_all_components_blocked():
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128, 256),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} for seed in range(8)})
    zero_delta = owner.paired_delta(full, full, paired_ci_min_seeds=8)
    matrix = {}
    for component in owner.COMPONENTS:
        matrix[f"DGT_without_{component}"] = {
            **zero_delta,
            "by_steps": {str(step): zero_delta for step in run_spec.step_grid},
        }
    by_steps = projection._robustness_by_steps(matrix)
    claims = projection._stable_component_causal_claims(by_steps)
    boundary = projection._stable_boundary_ledger(by_steps, claims)

    assert projection._stable_causal_attribution(claims) == "none"
    assert claims == []
    assert sum(1 for row in boundary if row["component"] in owner.COMPONENTS and row["status"] == "blocked") == len(owner.COMPONENTS)
    null_rows = [row for row in boundary if row["component"] == "<all>"]
    assert len(null_rows) == 1
    assert null_rows[0]["blocked"] is True
    assert null_rows[0]["not_silent"] is True
    assert null_rows[0]["reason"] == owner.NULL_CAUSAL_REASON


def test_nabl2_hg2_rejects_allowed_claim_below_ci_threshold():
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128,),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)
    rows = [row for step in run_spec.step_grid for seed in run_spec.seed_list for arm in run_spec.arms for row in [_metric_row(step=step, seed=seed, arm=arm)]]
    full = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} | {"quality_q": 0.7} for seed in range(8)})
    ablated = _summary({seed: {metric: 0.5 for metric in owner.METRIC_KEYS} | {"quality_q": 0.6} for seed in range(8)})
    delta = owner.paired_delta(full, ablated, paired_ci_min_seeds=8)
    by_steps = projection._robustness_by_steps(_matrix_with_component("LAT", delta))
    claim = {
        "component": "LAT",
        "claim_status": "allowed",
        "claim_scope": "bounded toy training",
        "evidence_scope": list(owner.COMPONENT_CAUSAL_EVIDENCE_SCOPE),
        "stable_step_settings": [128],
        "ci_low_metrics": {"quality_q": owner.MEASURABLE_EFFECT_THRESHOLD},
    }
    hardgates = projection._nabl2_hardgates(
        rows=rows,
        robustness_by_steps=by_steps,
        claims=[claim],
        boundary=projection._stable_boundary_ledger(by_steps, [claim]),
        compute_ledger=projection._compute_ledger(rows),
        source_audit={"status": "pass"},
        negative_witness_sweep={"status": "pass"},
    )

    assert by_steps["128"]["components"]["LAT"]["status"] == "allowed"
    assert hardgates["gates"]["NABL2-HG2"]["status"] == "fail"


def test_compute_ledger_records_steps_seed_and_units():
    run_spec = owner.DgtNeuralAblationRunSpec(
        step_grid=(128, 256),
        seed_count=8,
        seed_list=tuple(range(8)),
        requested_device="cpu",
    )
    projection = owner.DgtNeuralAblationRobustnessProjection(run_spec)
    rows = [
        _metric_row(step=step, seed=seed, arm=arm)
        for step in run_spec.step_grid
        for seed in run_spec.seed_list
        for arm in run_spec.arms
    ]

    ledger = projection._compute_ledger(rows)

    assert {"train_steps", "seed", "arm"}.issubset(set(ledger["dimensions"]))
    assert ledger["training_matrix_count"] == 176
    assert all({"train_steps", "seed", "device", "compute_units", "parameter_count", "optimizer_steps", "wall_time_proxy"} <= set(row) for row in ledger["rows"])


def test_nabl_hardgates_and_hg7_boundary_fail_closed():
    payload = owner.build_payload(
        generated_at="fixture",
        requested_device="cpu",
        run_spec=owner.DgtNeuralAblationRunSpec.quick_test(),
    )

    owner.validate_payload(payload)
    assert payload["pure_hardgates"]["status"] == "pass"
    assert payload["nabl_hardgates"]["status"] in {"pass", "fail"}
    assert payload["stable_causal_attribution"] in {"none", "partial", "complete"}
    assert set(payload["nabl_hardgates"]["gates"]) == set(owner.HG_IDS)
    assert set(payload["nabl2_hardgates"]["gates"]) == set(owner.NABL2_HG_IDS)
    assert set(payload["pure_hardgates"]["gates"]) == set(owner.PURE_HG_IDS)
    blocked = [row for row in payload["boundary_ledger"] if row["claim_blocked"] and row["component"] in owner.COMPONENTS]
    claimed = {row["component"] for row in payload["component_causal_claims"]}
    assert claimed.isdisjoint({row["component"] for row in blocked})
    assert {row["reason"] for row in blocked} <= {"NABL2-HG2", "NABL2-HG3"}
    assert {
        tuple(row["evidence_scope"])
        for row in payload["stable_component_causal_claims"]
        if row["claim_status"] == "allowed"
    } <= {("small-real-training",)}
    assert payload["compute_ledger"]["training_matrix_count"] == len(owner.ARM_IDS) * 2


def test_unavailable_payload_has_no_positive_component_claim():
    payload = owner.unavailable_payload(generated_at="fixture", requested_device="auto", reason="torch unavailable")

    owner.validate_payload(payload)
    assert payload["training_protocol"]["status"] == "unavailable"
    assert payload["stable_causal_attribution"] == "unavailable"
    assert payload["pure_hardgates"]["status"] == "fail"
    assert payload["nabl_hardgates"]["status"] == "fail"
    assert payload["nabl2_hardgates"]["status"] == "fail"
    assert payload["component_causal_claims"] == []


def test_metric_protocol_rejects_component_lookup_channels():
    payload = owner.build_payload(
        generated_at="fixture",
        requested_device="cpu",
        run_spec=owner.DgtNeuralAblationRunSpec.quick_test(),
    )

    assert payload["metric_protocol"]["purity_audit"]["status"] == "pass"
    assert set(payload["metric_protocol"]["inputs"]) == set(owner.OUTCOME_FIELDS)
    assert "disabled_component" not in payload["metric_protocol"]["inputs"]
    assert "removed_component" not in payload["metric_protocol"]["inputs"]


def test_owner_source_has_no_component_lookup_channels():
    source = inspect.getsource(owner)

    forbidden_tokens = (
        "COMPONENT_EFFECTS",
        "component_effects",
        "effect_prior",
        "per_component_quality",
        "per_component_penalty",
    )
    assert all(token not in source for token in forbidden_tokens)


def test_forbidden_positive_claim_terms_are_audited():
    mutated = _payload_with_synthetic_claim()
    mutated["component_causal_claims"][0]["claim_text"] = "global superiority"
    mutated["forbidden_claim_term_audit"] = owner._forbidden_claim_term_audit(
        {"claims": mutated["component_causal_claims"]}
    )

    with pytest.raises(ValueError, match="forbidden term audit"):
        owner.validate_payload(mutated)


@pytest.mark.parametrize(
    "evidence_scope",
    [
        None,
        "small-real-training",
        [],
        ["small-real-training", "small-real-training"],
        ["outside-enum"],
    ],
)
def test_component_causal_claim_rejects_invalid_evidence_scope(evidence_scope):
    mutated = _payload_with_synthetic_claim()
    mutated["component_causal_claims"][0]["evidence_scope"] = evidence_scope

    with pytest.raises(ValueError, match="component claim 0 evidence_scope"):
        owner.validate_payload(mutated)


def test_write_artifacts_emits_canonical_run_capsule_report_metrics_and_fingerprint(tmp_path):
    payload = owner.build_payload(
        generated_at="fixture",
        requested_device="cpu",
        run_spec=owner.DgtNeuralAblationRunSpec.quick_test(),
    )

    owner.write_artifacts(payload, root=tmp_path, generated_at="fixture")

    emitted = [
        owner.CANONICAL_JSON_ARTIFACT,
        owner.CANONICAL_MARKDOWN_ARTIFACT,
        owner.CANONICAL_FINGERPRINT_ARTIFACT,
        payload["run_artifacts"]["summary"],
        payload["run_artifacts"]["raw_metrics"],
        payload["run_artifacts"]["claim_capsule"],
        payload["run_artifacts"]["report"],
    ]
    assert all((tmp_path / artifact).exists() for artifact in emitted)

    capsule = json.loads((tmp_path / payload["run_artifacts"]["claim_capsule"]).read_text(encoding="utf-8"))
    assert capsule["owner_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$"
    assert capsule["hardgate_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$.nabl_hardgates.status"
    assert capsule["component_claim_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$.component_causal_claims"
    assert capsule["claim_count"] == len(payload["component_causal_claims"])

    raw_rows = (tmp_path / payload["run_artifacts"]["raw_metrics"]).read_text(encoding="utf-8").splitlines()
    assert len(raw_rows) == len(payload["records"])
    assert json.loads(raw_rows[0])["arm_id"] == owner.ARM_IDS[0]

    markdown = (tmp_path / owner.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    assert "# DGT neural ablation" in markdown
    assert f"- Status: `{payload['nabl_hardgates']['status']}`" in markdown
    assert f"- Stable causal attribution: `{payload['stable_causal_attribution']}`" in markdown
    assert f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}:$`" in markdown

    fingerprint = json.loads((tmp_path / owner.CANONICAL_FINGERPRINT_ARTIFACT).read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "dgt-neural-ablation"
    assert len(fingerprint["input_fingerprint"]) == 64
    assert len(fingerprint["output_digest"]) == 64
    assert fingerprint["generated_by"]["generated_at"] == "fixture"


def test_cli_main_writes_cpu_artifact_layout(tmp_path, capsys):
    exit_code = runner.main(["--root", str(tmp_path), "--generated-at", "fixture", "--requested-device", "cpu", "--quick-test"])

    assert exit_code == 0
    summary = json.loads(capsys.readouterr().out)
    assert summary["artifact_id"] == owner.ARTIFACT_ID
    payload = json.loads((tmp_path / owner.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert summary["status"] == payload["nabl_hardgates"]["status"]
    assert summary["training_status"] == payload["training_protocol"]["status"]
    assert summary["stable_causal_attribution"] == payload["stable_causal_attribution"]
    assert summary["device"] == "cpu"
    assert summary["step_grid"] == [8]
    assert summary["seed_count"] == 2
    assert summary["arm_count"] == len(owner.ARM_IDS)
    assert summary["claim_count"] == len(
        owner.build_payload(
            generated_at="fixture",
            requested_device="cpu",
            run_spec=owner.DgtNeuralAblationRunSpec.quick_test(),
        )["component_causal_claims"]
    )

    assert (tmp_path / owner.CANONICAL_JSON_ARTIFACT).exists()
    assert (tmp_path / owner.CANONICAL_MARKDOWN_ARTIFACT).exists()
    assert (tmp_path / owner.CANONICAL_FINGERPRINT_ARTIFACT).exists()
    assert (tmp_path / owner.RUN_ROOT / "summary.json").exists()
    assert (tmp_path / owner.RUN_ROOT / "raw_metrics.jsonl").exists()
    assert (tmp_path / owner.RUN_ROOT / "claim_capsule.json").exists()
    assert (tmp_path / owner.RUN_ROOT / "report.md").exists()

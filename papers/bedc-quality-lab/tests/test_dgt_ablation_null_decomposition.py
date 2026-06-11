import copy
import json
from pathlib import Path

from bedc_quality_lab import dgt_ablation_null_decomposition as nd


def _component(component: str, *, quality_delta: float = 0.02, ci_low: float = 0.01, ci_high: float = 0.03) -> tuple[str, dict]:
    arm = f"DGT_without_{component}"
    return arm, {
        "arm_summaries": {
            arm: {
                "disabled_component": component,
                "metrics": {"quality_q": 0.84 - quality_delta},
            }
        },
        "paired_delta_matrix": {
            arm: {
                "metrics": {"quality_q": quality_delta},
                "confidence_intervals": {"quality_q": {"low": ci_low, "high": ci_high}},
                "paired_seed_count": 8,
                "paired_ci_min_seeds": 8,
            }
        },
    }


def source_fixture() -> dict:
    components = [f"C{i}" for i in range(10)]
    source = {
        "run_spec": {"arms": ["full_DGT"] + [f"DGT_without_{component}" for component in components]},
        "module_registry": {
            "full_DGT": {"disabled_component": None},
        },
        "arm_summaries": {
            "full_DGT": {"disabled_component": None, "metrics": {"quality_q": 0.84}},
        },
        "paired_delta_matrix": {},
    }
    for component in components:
        arm, payload = _component(component)
        source["module_registry"][arm] = {"disabled_component": component}
        source["arm_summaries"].update(payload["arm_summaries"])
        source["paired_delta_matrix"].update(payload["paired_delta_matrix"])
    return source


def build(source: dict, tmp_path: Path) -> dict:
    return nd.build_payload(root=tmp_path, source_payload=source, generated_at="fixture")


def test_missing_source_fails_closed(tmp_path):
    payload = nd.build_payload(root=tmp_path, generated_at="fixture")
    null = payload["null_decomposition"]

    assert payload["source_artifact"]["status"] == "missing"
    assert payload["hardgates"]["ND-HG1"]["status"] == "fail"
    assert null["analysis_status"] == "fail"
    assert null["verdict"] == "unresolved"
    assert null["roadmap_recommendation"] == "repair-evidence"


def test_missing_required_groups_fail_closed(tmp_path):
    cases = [
        ("metric", lambda item: item["arm_summaries"]["DGT_without_C0"]["metrics"].pop("quality_q")),
        ("leave_one_out", lambda item: item["paired_delta_matrix"]["DGT_without_C0"]["metrics"].pop("quality_q")),
        ("paired_ci", lambda item: item["paired_delta_matrix"]["DGT_without_C0"].pop("confidence_intervals")),
    ]
    for _, mutate in cases:
        source = source_fixture()
        mutate(source)
        payload = build(source, tmp_path)

        assert payload["null_decomposition"]["analysis_status"] == "fail"
        assert payload["null_decomposition"]["verdict"] == "unresolved"
        assert payload["null_decomposition"]["roadmap_recommendation"] == "repair-evidence"
        assert payload["null_decomposition"]["components"][0]["classification"] == "unresolved"


def test_underpowered_signal_comes_from_numeric_ci_mutation(tmp_path):
    source = source_fixture()
    row = source["paired_delta_matrix"]["DGT_without_C0"]
    row["metrics"]["quality_q"] = 0.02
    row["confidence_intervals"]["quality_q"] = {"low": -0.02, "high": 0.05}
    source["arm_summaries"]["DGT_without_C0"]["metrics"]["quality_q"] = 0.82

    payload = build(source, tmp_path)
    component = payload["null_decomposition"]["components"][0]

    assert component["signals"]["underpowered"]["active"] is True
    assert "underpowered" in component["active_signals"]

    narrowed = copy.deepcopy(source)
    narrowed["paired_delta_matrix"]["DGT_without_C0"]["confidence_intervals"]["quality_q"] = {"low": 0.01, "high": 0.03}
    narrowed_payload = build(narrowed, tmp_path)
    narrowed_component = narrowed_payload["null_decomposition"]["components"][0]

    assert narrowed_component["signals"]["underpowered"]["active"] is False
    assert "underpowered" not in narrowed_component["active_signals"]


def test_component_with_two_active_predicates_is_mixed(tmp_path):
    source = source_fixture()
    row = source["paired_delta_matrix"]["DGT_without_C0"]
    row["metrics"]["quality_q"] = 0.0001
    row["confidence_intervals"]["quality_q"] = {"low": 0.0, "high": 0.0002}
    source["arm_summaries"]["DGT_without_C0"]["metrics"]["quality_q"] = 0.8399

    payload = build(source, tmp_path)
    component = payload["null_decomposition"]["components"][0]

    assert component["signals"]["saturation"]["active"] is True
    assert component["signals"]["redundancy"]["active"] is True
    assert component["classification"] == "mixed"
    assert component["active_signals"] == ["saturation", "redundancy"]


def test_global_mixed_cases_remain_first_class(tmp_path):
    source = source_fixture()
    for index in range(6):
        arm = f"DGT_without_C{index}"
        source["paired_delta_matrix"][arm]["metrics"]["quality_q"] = 0.002
        source["paired_delta_matrix"][arm]["confidence_intervals"]["quality_q"] = {"low": 0.001, "high": 0.003}
        source["arm_summaries"][arm]["metrics"]["quality_q"] = 0.838
    for index in range(6, 10):
        arm = f"DGT_without_C{index}"
        source["paired_delta_matrix"][arm]["metrics"]["quality_q"] = 0.0001
        source["paired_delta_matrix"][arm]["confidence_intervals"]["quality_q"] = {"low": 0.0, "high": 0.0002}
        source["arm_summaries"][arm]["metrics"]["quality_q"] = 0.8399

    payload = build(source, tmp_path)
    null = payload["null_decomposition"]

    assert null["analysis_status"] == "pass"
    assert null["global_counts"]["saturation"] == 6
    assert null["global_counts"]["mixed"] == 4
    assert null["verdict"] == "mixed"
    assert null["roadmap_recommendation"] == "mixed"
    assert null["roadmap_priority"]


def test_dominant_component_mixed_produces_global_mixed(tmp_path):
    source = source_fixture()
    for index in range(8):
        arm = f"DGT_without_C{index}"
        source["paired_delta_matrix"][arm]["metrics"]["quality_q"] = 0.0001
        source["paired_delta_matrix"][arm]["confidence_intervals"]["quality_q"] = {"low": 0.0, "high": 0.0002}
        source["arm_summaries"][arm]["metrics"]["quality_q"] = 0.8399

    payload = build(source, tmp_path)
    null = payload["null_decomposition"]

    assert null["global_counts"]["mixed"] == 10
    assert null["verdict"] == "mixed"
    assert null["roadmap_recommendation"] == "mixed"


def test_output_does_not_copy_raw_training_rows(tmp_path):
    source = source_fixture()
    source["records"] = [{"seed": 1, "raw": "do-not-copy"}]

    payload = build(source, tmp_path)
    serialized = json.dumps(payload, sort_keys=True)

    assert "do-not-copy" not in serialized
    assert payload["source_artifact"]["path"] == nd.SOURCE_ARTIFACT
    assert payload["source_artifact"]["json_pointer"] == "$"

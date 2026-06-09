import json
from copy import deepcopy

import pytest

from bedc_quality_lab.causal_patch_suite import (
    JSON_ARTIFACT,
    PATCH_HARDGATES,
    PATCH_TYPES,
    SOURCE_ARTIFACTS,
    audit_causal_patch_suite,
    build_causal_patch_suite,
)
from scripts import run_causal_patch_suite as runner


def _source_payloads():
    root = runner.ROOT
    return {
        name: json.loads((root / artifact).read_text(encoding="utf-8"))
        if (root / artifact).exists()
        else None
        for name, artifact in SOURCE_ARTIFACTS.items()
    }


def _dgt_pointer_contract(*, key="dgt_mechanism_cert", evidence_pointer=None, hardgate_pointers=None):
    return {
        key: {
            "patch_evidence_pointer": evidence_pointer or f"{JSON_ARTIFACT}:$.dgt_mechanism_cert",
            "patch_hardgate_pointers": hardgate_pointers
            or {gate: f"{JSON_ARTIFACT}:$.hardgates.{gate}" for gate in PATCH_HARDGATES},
        }
    }


def _passing_source_payloads():
    return {
        "gap_head_on_h": {
            "treatment_comparison": {
                "failure_detection_auroc_delta_learned_minus_vanilla": {
                    "ci95_low": 0.1,
                    "ci95_high": 0.2,
                }
            },
            "gap_channel_metadata": [{"channel": "gap"}],
            "control_protocol": {
                "audit_status": "pass",
                "same_budget_as_treatment": True,
            },
            "treatment_verdict": {"status": "pass"},
            "scope_seal": {
                "status": "closed",
                "production_forbidden": True,
            },
        },
        "gap_head_ablation": {
            "factor_attribution": {
                "learned_head": {
                    "status": "pass",
                    "ci95_low": 0.1,
                    "auroc_drop_ci95": {
                        "ci95_low": 0.1,
                        "ci95_high": 0.2,
                    },
                }
            }
        },
        "gap_head_attribution_capsule": {
            "head_channel_patch_evidence": {
                "gate_status": "pass",
                "causal_patch_claim": {"status": "pass"},
            },
            "score_margin_causal_evidence": {
                "status": "pass",
                "channel_classification": "mechanism",
            },
        },
        "discovery_gated_transformer": _dgt_pointer_contract(),
    }


def _records_by_type(payload):
    return {row["patch_type"]: row for row in payload["patch_records"]}


def _recursive_keys(value):
    if isinstance(value, dict):
        for key, child in value.items():
            yield key
            yield from _recursive_keys(child)
    elif isinstance(value, list):
        for child in value:
            yield from _recursive_keys(child)


def test_patch_taxonomy_is_exact_and_unique():
    assert PATCH_TYPES == (
        "attention-route",
        "ledger-head",
        "gap-head",
        "D1 feature",
        "D2 interaction",
        "D3 composition",
        "mechanism probe",
        "scope-seal",
    )
    assert len(set(PATCH_TYPES)) == len(PATCH_TYPES)
    assert PATCH_HARDGATES == ("PATCH-HG1", "PATCH-HG2", "PATCH-HG3", "PATCH-HG4", "PATCH-HG5", "PATCH-HG6")


def test_suite_projects_source_backed_rows_and_fails_closed_for_dgt_pointer_consumer():
    payload = build_causal_patch_suite(source_artifacts=_source_payloads(), generated_at="fixture")
    rows = {row["patch_type"]: row for row in payload["patch_records"]}

    assert tuple(payload["patch_types"]) == PATCH_TYPES
    assert set(rows) == set(PATCH_TYPES)
    assert rows["gap-head"]["source_pointer"] == "$.head_channel_patch_evidence"
    assert rows["mechanism probe"]["source_pointer"] == "$.score_margin_causal_evidence"
    assert rows["D3 composition"]["status"] == "present-but-fail-closed"
    assert payload["hardgates"]["PATCH-HG6"]["status"] in {"missing_evidence", "present-but-fail-closed"}
    assert payload["dgt_mechanism_cert"]["status"] == "present-but-fail-closed"
    assert payload["dgt_mechanism_cert"]["patch_evidence_pointer"] == f"{JSON_ARTIFACT}:$.dgt_mechanism_cert"


def test_missing_source_rows_are_explicit_not_omitted():
    sources = _source_payloads()
    sources["gap_head_attribution_capsule"] = None
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = {row["patch_type"]: row for row in payload["patch_records"]}

    assert rows["gap-head"]["status"] == "missing_evidence"
    assert rows["mechanism probe"]["status"] == "missing_evidence"
    assert set(rows) == set(PATCH_TYPES)
    assert payload["hardgates"]["PATCH-HG1"]["status"] == "missing_evidence"


def test_dgt_pointer_contract_passes_only_when_consumer_contains_resolved_pointers():
    sources = _source_payloads()
    sources["discovery_gated_transformer"] = _dgt_pointer_contract()
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")

    assert payload["hardgates"]["PATCH-HG6"]["status"] == "pass"


def test_minimal_passing_sources_satisfy_all_patch_hardgates():
    payload = build_causal_patch_suite(source_artifacts=_passing_source_payloads(), generated_at="fixture")

    assert {gate["status"] for gate in payload["hardgates"].values()} == {"pass"}
    assert payload["dgt_mechanism_cert"]["status"] == "pass"


@pytest.mark.parametrize(
    ("source_name", "expected_rows"),
    (
        ("gap_head_on_h", ("attention-route", "D1 feature", "D2 interaction", "D3 composition", "scope-seal")),
        ("gap_head_ablation", ("ledger-head",)),
        ("gap_head_attribution_capsule", ("gap-head", "mechanism probe")),
    ),
)
def test_missing_source_payloads_fail_closed_without_omitting_patch_rows(source_name, expected_rows):
    sources = _passing_source_payloads()
    sources[source_name] = None
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    for patch_type in expected_rows:
        assert rows[patch_type]["status"] == "missing_evidence"
    assert payload["hardgates"]["PATCH-HG1"]["status"] == "missing_evidence"


@pytest.mark.parametrize(
    ("mutate", "patch_type", "expected_status", "failed_gate"),
    (
        (
            lambda sources: sources["gap_head_on_h"]["treatment_comparison"]
            .__setitem__("failure_detection_auroc_delta_learned_minus_vanilla", {"ci95_low": -0.1, "ci95_high": 0.2}),
            "attention-route",
            "present-but-fail-closed",
            "PATCH-HG3",
        ),
        (
            lambda sources: sources["gap_head_on_h"].__setitem__("treatment_comparison", {}),
            "attention-route",
            "missing_evidence",
            "PATCH-HG3",
        ),
        (
            lambda sources: sources["gap_head_ablation"]["factor_attribution"]["learned_head"]
            .__setitem__("auroc_drop_ci95", {"ci95_low": 0.0, "ci95_high": 0.1}),
            "ledger-head",
            "present-but-fail-closed",
            "PATCH-HG3",
        ),
        (
            lambda sources: sources["gap_head_ablation"]["factor_attribution"]["learned_head"].__setitem__("auroc_drop_ci95", {}),
            "ledger-head",
            "missing_evidence",
            "PATCH-HG3",
        ),
        (
            lambda sources: sources["gap_head_attribution_capsule"]["head_channel_patch_evidence"]
            .__setitem__("gate_status", "fail"),
            "gap-head",
            "present-but-fail-closed",
            "PATCH-HG3",
        ),
    ),
)
def test_treatment_separation_inputs_fail_closed_at_patch_hardgate(mutate, patch_type, expected_status, failed_gate):
    sources = _passing_source_payloads()
    mutate(sources)
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    assert rows[patch_type]["status"] == expected_status
    assert payload["hardgates"][failed_gate]["status"] == "present-but-fail-closed"


def test_empty_gap_metadata_fails_closed_without_promoting_target_isolation():
    sources = _passing_source_payloads()
    sources["gap_head_on_h"]["gap_channel_metadata"] = []
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    assert rows["D1 feature"]["status"] == "missing_evidence"
    assert payload["hardgates"]["PATCH-HG1"]["status"] == "missing_evidence"


def test_failed_control_audit_fails_closed_at_matched_control_hardgate():
    sources = _passing_source_payloads()
    sources["gap_head_on_h"]["control_protocol"]["audit_status"] = "fail"
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    assert rows["D2 interaction"]["status"] == "present-but-fail-closed"
    assert payload["matched_controls"]["status"] == "present-but-fail-closed"
    assert payload["hardgates"]["PATCH-HG4"]["status"] == "present-but-fail-closed"


@pytest.mark.parametrize(
    "scope_seal",
    (
        {"status": "open", "production_forbidden": True},
        {"status": "closed", "production_forbidden": False},
    ),
)
def test_open_or_production_allowed_scope_fails_closed_at_side_effect_hardgate(scope_seal):
    sources = _passing_source_payloads()
    sources["gap_head_on_h"]["scope_seal"] = scope_seal
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    assert rows["scope-seal"]["status"] == "present-but-fail-closed"
    assert payload["side_effect_ledger"]["status"] == "present-but-fail-closed"
    assert payload["hardgates"]["PATCH-HG5"]["status"] == "present-but-fail-closed"


def test_non_pass_attribution_status_fails_closed_for_mechanism_probe_row():
    sources = _passing_source_payloads()
    sources["gap_head_attribution_capsule"]["score_margin_causal_evidence"]["status"] = "fail"
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")
    rows = _records_by_type(payload)

    assert rows["mechanism probe"]["status"] == "present-but-fail-closed"


@pytest.mark.parametrize(
    "dgt_payload",
    (
        _dgt_pointer_contract(key="wrong_cert_key"),
        _dgt_pointer_contract(evidence_pointer="reports/canonical/causal-patch-suite.json:$.wrong_pointer"),
        _dgt_pointer_contract(hardgate_pointers={"PATCH-HG1": f"{JSON_ARTIFACT}:$.hardgates.PATCH-HG1"}),
    ),
)
def test_malformed_dgt_pointer_contract_fails_closed(dgt_payload):
    sources = _passing_source_payloads()
    sources["discovery_gated_transformer"] = dgt_payload
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")

    assert payload["hardgates"]["PATCH-HG6"]["status"] == "present-but-fail-closed"
    assert payload["dgt_mechanism_cert"]["status"] == "present-but-fail-closed"


def test_not_claimed_excludes_production_global_mechanism_tensor_namecert_and_llm_quality():
    payload = build_causal_patch_suite(source_artifacts=_source_payloads(), generated_at="fixture")
    text = " ".join(payload["not_claimed"]).lower()

    for expected in ("production causality", "global model superiority", "full mechanism closure", "full tensornamecert", "llm behavior quality"):
        assert expected in text


def test_audit_rejects_forbidden_surfaces_recursively():
    payload = build_causal_patch_suite(source_artifacts=_source_payloads(), generated_at="fixture")
    mutated = deepcopy(payload)
    mutated["dgt_mechanism_cert"]["terminal_verdict"] = "forbidden"

    assert "terminal_verdict" not in set(_recursive_keys(payload))
    assert audit_causal_patch_suite(payload)["status"] == "pass"
    assert audit_causal_patch_suite(mutated)["status"] == "fail"


@pytest.mark.parametrize(
    ("mutate", "expected_failure"),
    (
        (lambda payload: payload.pop("patch_records"), "missing:patch_records"),
        (lambda payload: payload.__setitem__("patch_types", ["attention-route"]), "patch-types-mismatch"),
        (lambda payload: payload["hardgates"].pop("PATCH-HG6"), "hardgate-set-mismatch"),
        (lambda payload: payload.__setitem__("producer", ".refactor-loop/host.env"), "forbidden-surface"),
        (lambda payload: payload["patch_records"][0].__setitem__("source_artifact", "causal-patch-suite-dgt"), "forbidden-surface"),
    ),
)
def test_audit_rejects_required_key_taxonomy_hardgate_and_forbidden_surface_failures(mutate, expected_failure):
    payload = build_causal_patch_suite(source_artifacts=_passing_source_payloads(), generated_at="fixture")
    mutated = deepcopy(payload)
    mutate(mutated)

    audit = audit_causal_patch_suite(mutated)
    assert audit["status"] == "fail"
    assert expected_failure in audit["failures"]


def test_write_artifacts_raises_when_audit_fails(monkeypatch, tmp_path):
    payload = build_causal_patch_suite(source_artifacts=_passing_source_payloads(), generated_at="fixture")
    payload["patch_records"][0]["source_artifact"] = "causal-patch-suite-dgt"
    monkeypatch.setattr(runner, "build_payload", lambda *, root, generated_at=None: payload)

    with pytest.raises(ValueError, match="causal patch suite audit failed"):
        runner.write_artifacts(root=tmp_path, generated_at="fixture")


def test_write_artifacts_creates_only_suite_json_and_markdown(tmp_path):
    root = runner.ROOT
    for artifact in SOURCE_ARTIFACTS.values():
        source = root / artifact
        if source.exists():
            target = tmp_path / artifact
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source.read_text(encoding="utf-8"), encoding="utf-8")

    paths = runner.write_artifacts(root=tmp_path, generated_at="fixture")

    assert set(paths) == {"json", "markdown"}
    assert paths["json"].relative_to(tmp_path).as_posix() == "reports/canonical/causal-patch-suite.json"
    assert paths["markdown"].relative_to(tmp_path).as_posix() == "reports/canonical/causal-patch-suite.md"
    payload = json.loads(paths["json"].read_text(encoding="utf-8"))
    report = paths["markdown"].read_text(encoding="utf-8")
    assert payload["schema_id"] == "bedc-quality-lab:causal-patch-suite"
    assert "# Causal Patch Suite" in report

import json
from copy import deepcopy

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
    sources["discovery_gated_transformer"] = {
        "dgt_mechanism_cert": {
            "patch_evidence_pointer": f"{JSON_ARTIFACT}:$.dgt_mechanism_cert",
            "patch_hardgate_pointers": {
                gate: f"{JSON_ARTIFACT}:$.hardgates.{gate}" for gate in PATCH_HARDGATES
            },
        }
    }
    payload = build_causal_patch_suite(source_artifacts=sources, generated_at="fixture")

    assert payload["hardgates"]["PATCH-HG6"]["status"] == "pass"


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

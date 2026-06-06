import json
from pathlib import Path

import pytest

from bedc_quality_lab.discovery_compiler.pointers import pointer_value, split_artifact_pointer, resolve_artifact_pointer
from bedc_quality_lab.discovery_compiler.negative_reports import (
    BedcGapMapping,
    DIMENSION_MISMATCH_GAP_WITNESS_POINTER,
    DIMENSION_MISMATCH_REGRESSION_NODEID,
    DIMENSION_MISMATCH_REPORT_ID,
    REQUIRED_NEGATIVE_REPORT_IDS,
    validate_negative_report_row,
)


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "bedc_quality_lab" / "discovery_compiler"
SCRIPTS = ROOT / "scripts"


def _load_json(artifact: str):
    return json.loads((ROOT / artifact).read_text(encoding="utf-8"))


def _pointer_cells(value):
    if isinstance(value, dict):
        artifact = value.get("json_artifact")
        for key, cell in value.items():
            if key.endswith("pointer") and isinstance(cell, str) and ":$." in cell:
                yield cell
            elif key.endswith("pointer") and isinstance(cell, str) and cell.startswith("$.") and isinstance(artifact, str):
                yield f"{artifact}:{cell}"
            yield from _pointer_cells(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _pointer_cells(cell)


def _recursive_values(value):
    if isinstance(value, dict):
        for key, item in value.items():
            yield key
            yield from _recursive_values(item)
    elif isinstance(value, list):
        for item in value:
            yield from _recursive_values(item)
    else:
        yield value


def _dimension_mismatch_owner():
    reports = _load_json("reports/canonical/negative_discovery_reports.json")
    return next(row for row in reports["rows"] if row["report_id"] == DIMENSION_MISMATCH_REPORT_ID)


def test_discovery_map_pointer_cells_resolve_against_canonical_artifacts():
    payload = _load_json("reports/canonical/discovery_map.json")
    pointers = list(_pointer_cells(payload["rows"]))

    assert pointers
    for pointer in pointers:
        assert split_artifact_pointer(pointer) is not None
        assert resolve_artifact_pointer(ROOT, pointer) is not None


def test_discovery_map_does_not_copy_negative_report_body_cells():
    discovery = _load_json("reports/canonical/discovery_map.json")
    reports = _load_json("reports/canonical/negative_discovery_reports.json")
    forbidden = {
        "terminal_verdict",
        "classifier_reasons",
        "failed_gate",
        "debt_row_pointer",
        "anti_triviality_status",
        "downgrade_reason",
        "effective_level",
        "hypothesis",
        "not_claimed",
        "what_was_learned",
    }

    owners = {row["negative_id"]: row for row in reports["rows"]}
    dn_rows = [row for row in discovery["rows"] if row["discovery_level"] == "DN"]
    assert dn_rows
    for row in dn_rows:
        assert not (set(row) & forbidden)
        pointer = row["negative_report_pointer"]
        owner = resolve_artifact_pointer(ROOT, pointer)
        negative_id = (
            "dn:dimension-mismatch-scale-leakage"
            if row["report"] == "dimension-mismatch-debt-transfer"
            else f"dn:{row['report']}"
        )
        assert owner == owners[negative_id]
        assert owner["terminal_verdict"]


def test_negative_discovery_reports_are_canonical_owner_for_required_dn_ids():
    reports = _load_json("reports/canonical/negative_discovery_reports.json")
    rows = reports["rows"]
    report_ids = {row["report_id"] for row in rows}

    assert REQUIRED_NEGATIVE_REPORT_IDS <= report_ids
    assert not any(row["kind"] == "witness" for row in rows)
    for row in rows:
        assert row["kind"] == "discovery_report"
        assert row["negative_id"] == f"dn:{row['report_id']}"
        assert row["failed_gate"]
        assert row["what_was_learned"]
        assert row.get("next_hypothesis") or row.get("stop_reason")
        assert resolve_artifact_pointer(ROOT, row["source"]) is not None
        assert resolve_artifact_pointer(ROOT, row["ledger_pointer"]) is not None
    dimension = next(row for row in rows if row["report_id"] == "dimension-mismatch-scale-leakage")
    assert dimension["claim_id"] == "claim:dimension-mismatch-debt-transfer"
    assert dimension["base_level"] == "D4"
    assert dimension["effective_level"] == "DN"
    assert dimension["failed_gate"] == "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    assert set(dimension["bedc_gap_mapping"]) == {
        "source_witness_pointer",
        "bedc_gap_field",
        "demotion_rule",
        "regression_test",
    }


def test_dimension_mismatch_bedc_gap_mapping_owner_cell_matches_source_witness():
    owner = _dimension_mismatch_owner()
    cell = owner["bedc_gap_mapping"]
    witness = resolve_artifact_pointer(ROOT, DIMENSION_MISMATCH_GAP_WITNESS_POINTER)
    capsule_artifact = DIMENSION_MISMATCH_GAP_WITNESS_POINTER.split(":", 1)[0]
    capsule = _load_json(capsule_artifact)

    assert cell == BedcGapMapping.from_witness_pointer(
        ROOT,
        DIMENSION_MISMATCH_GAP_WITNESS_POINTER,
    ).as_owner_cell()
    assert cell == {
        "source_witness_pointer": DIMENSION_MISMATCH_GAP_WITNESS_POINTER,
        "bedc_gap_field": witness["bedc_gap_field"],
        "demotion_rule": witness["demotion_rule"],
        "regression_test": witness["regression_test"],
    }
    assert pointer_value(capsule, cell["regression_test"]) == DIMENSION_MISMATCH_REGRESSION_NODEID


def test_dimension_mismatch_owner_source_evidence_and_demotion_cells_stay_bound_to_source_artifact():
    owner = _dimension_mismatch_owner()
    source_payload = _load_json(owner["json_artifact"])

    assert resolve_artifact_pointer(ROOT, owner["source"]) == "scale_leakage_detected"
    assert pointer_value(source_payload, owner["failed_gate"]) == "scale_leakage_detected"
    assert pointer_value(source_payload, owner["evidence_pointer"]) == "DN"
    assert owner["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"


def test_dimension_mismatch_bedc_gap_mapping_validator_fails_closed():
    owner = _dimension_mismatch_owner()

    missing = dict(owner)
    missing.pop("bedc_gap_mapping")
    with pytest.raises(ValueError, match="requires bedc_gap_mapping"):
        validate_negative_report_row(ROOT, missing)

    dangling = dict(owner)
    dangling["bedc_gap_mapping"] = {
        **owner["bedc_gap_mapping"],
        "source_witness_pointer": (
            "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:"
            "$.run_local.negative_witness[99]"
        ),
    }
    with pytest.raises(ValueError, match="witness pointer does not resolve"):
        validate_negative_report_row(ROOT, dangling)

    drifted = dict(owner)
    drifted["bedc_gap_mapping"] = {**owner["bedc_gap_mapping"], "bedc_gap_field": "other"}
    with pytest.raises(ValueError, match="does not match source witness"):
        validate_negative_report_row(ROOT, drifted)


def test_dn_verdict_rows_are_pointer_only_and_resolve_to_canonical_owner():
    rows = [
        json.loads(line)
        for line in (ROOT / "reports/canonical/claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    dn_rows = [row for row in rows if "negative_report_pointer" in row]

    assert dn_rows
    for row in dn_rows:
        assert set(row) == {
            "claim_id",
            "claim_graph_node_id",
            "claim_verdict",
            "reason",
            "negative_report_pointer",
        }
        assert resolve_artifact_pointer(ROOT, row["negative_report_pointer"]) is not None


def test_dimension_mismatch_public_surfaces_do_not_copy_bedc_gap_mapping_cells():
    forbidden = {
        "bedc_gap_mapping",
        "bedc_gap_field",
        "demotion_rule",
        "regression_test",
        DIMENSION_MISMATCH_REGRESSION_NODEID,
    }
    surfaces = [
        _load_json("reports/canonical/discovery_map.json"),
        _load_json("reports/canonical/discovery_negative_witness_summary.json"),
        _load_json("reports/canonical/index.json"),
        [
            json.loads(line)
            for line in (ROOT / "reports/canonical/claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
            if line
        ],
    ]

    for surface in surfaces:
        values = {str(value) for value in _recursive_values(surface)}
        assert not (forbidden & values)


def test_negative_discovery_artifacts_are_written_only_by_core():
    allowed = {
        "bedc_quality_lab/discovery_compiler/negative_reports.py",
        "bedc_quality_lab/discovery_compiler/compiler.py",
        "scripts/run_discovery_negative_witness_summary.py",
    }
    writers = []
    for path in list(CORE.glob("*.py")) + list(SCRIPTS.glob("run_*.py")):
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        if "negative_discovery_reports" not in text and "discovery_negative_witness_summary" not in text:
            continue
        writes_negative_file = rel == "bedc_quality_lab/discovery_compiler/negative_reports.py" and "write_text(" in text
        calls_negative_writer = "write_negative_discovery_reports(" in text or "write_negative_witness_summary(" in text
        if writes_negative_file or calls_negative_writer:
            writers.append(rel)

    assert sorted(writers) == sorted(allowed)


def test_discovery_compiler_core_has_no_backend_terms_or_backend_imports():
    forbidden_terms = (
        "sigreg-training-proxy",
        "anisotropic-ou-sweep",
        "nongaussian-distribution-sweep",
        "mixing-family-sweep",
        "rho",
        "Gaussian",
        "SIGReg",
        "Hermite",
        "LeJEPA",
    )
    for path in CORE.glob("*.py"):
        text = path.read_text(encoding="utf-8")
        assert "bedc_quality_lab.backends" not in text
        assert "run_canonical_reports" not in text
        for term in forbidden_terms:
            assert term not in text

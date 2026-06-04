import json
from pathlib import Path

from bedc_quality_lab.discovery_compiler.pointers import split_artifact_pointer, resolve_artifact_pointer


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
        assert owner == owners[f"dn:{row['report']}"]
        assert owner["terminal_verdict"]


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
        "gap-head",
        "certificate-guided",
        "sigreg-training-proxy",
        "anisotropic-ou-sweep",
        "nongaussian-distribution-sweep",
        "mixing-family-sweep",
        "dimension-mismatch",
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

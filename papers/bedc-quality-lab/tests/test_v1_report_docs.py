import json
import re
from pathlib import Path

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts.check_v1_report_docs import (
    D4_DISCOVERY_LEVEL,
    JSON_POINTER_RE,
    SELECTED_WORKED_CASE_DISCOVERY_LEVEL,
    check_doc_hg_surfaces,
    check_literature_ledger,
    exclusive_positive_worked_case_hits,
    jsonpath_exists,
)
from scripts.literature_ledger import validate_literature_ledger
from scripts import run_canonical_reports as canonical
from tests.test_alpha_milestone_gate import HIDDEN_SCORECARD_TERMS


ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ROOT / "reports" / "canonical"
V1_REPORT = ROOT / "docs" / "bedc_quality_lab_v1.md"
V1_DOC_SURFACES = (
    V1_REPORT,
    ROOT / "docs" / "v1_report_outline.md",
    ROOT / "docs" / "claims_and_nonclaims.md",
    ROOT / "docs" / "bedc_quality_lab_alpha_milestone.md",
    ROOT / "docs" / "artifact_manifest.md",
)
OUTLINE_HEADINGS = (
    "## 1. Scope & honest boundary",
    "## 2. EvidenceEnvelope schema",
    "## 3. CostProtocol & quality_q",
    "## 4. Theorem-bound metrics",
    "## 5. TensorNameCertCandidate",
    "## 6. Canonical reports",
    "## 7. Selected positive worked case: gap-head-on-h",
    "## 8. Negative: certificate-guided",
    "## 9. Observed-debt: non-Gaussian",
    "## 10. Formal hardening",
    "## 11. Limitations",
    "## 12. Remote target",
)
SELECTED_WORKED_CASE_SENTENCE = (
    "`gap-head-on-h` is the selected positive worked case for this report frame; "
    "positive-discovery classification is read from "
    "`reports/canonical/discovery_map.json:$.rows[*]`, so this section does not "
    "claim uniqueness among positive rows. Its current operational level is D4, "
    "with D5-O readiness blocked by the ablation hardgate."
)
CANONICAL_JSON_RE = re.compile(r"^reports/canonical/[^`\s]+\.json$")
CANONICAL_JSON_WITH_POINTER_RE = re.compile(r"^(reports/canonical/[^`\s]+\.json):(\$.*)$")
CANONICAL_JSON_PAIR_RE = re.compile(r"^reports/canonical/([^`\s]+)\.\{json,md\}$")
CANONICAL_JSON_GLOB_RE = re.compile(r"^reports/canonical/\*\.\{json,md\}$")
MINIMAL_LEDGER_DOCS = {
    V1_REPORT: "`reports/canonical/index.json:$.literature_ledger`",
}
MINIMAL_LEDGER_INDEX = {
    "literature_ledger": {
        "status": "ready",
    },
}


def _phrase(*parts: str) -> str:
    return "".join(parts)


def _code_spans(text: str) -> list[str]:
    return re.findall(r"`([^`]+)`", text)


def _canonical_json_path(span: str) -> Path | None:
    if CANONICAL_JSON_RE.match(span):
        return ROOT / span
    if pair_match := CANONICAL_JSON_PAIR_RE.match(span):
        return CANONICAL / f"{pair_match.group(1)}.json"
    return None


def _extract_canonical_pointer_refs(text: str) -> list[tuple[str, str]]:
    refs: list[tuple[str, str]] = []
    current_json: str | None = None
    for line in text.splitlines():
        line_spans = _code_spans(line)
        for span in line_spans:
            if combined_match := CANONICAL_JSON_WITH_POINTER_RE.match(span.rstrip(".,;:")):
                refs.append((combined_match.group(1), combined_match.group(2)))
                continue
            if _canonical_json_path(span) is not None:
                current_json = span
                continue
            if CANONICAL_JSON_GLOB_RE.match(span):
                current_json = None
                continue
            pointer = span.rstrip(".,;:")
            if current_json is not None and JSON_POINTER_RE.match(pointer):
                refs.append((current_json, pointer))
    return list(dict.fromkeys(refs))


def test_v1_report_has_outline_sections():
    text = V1_REPORT.read_text(encoding="utf-8")
    positions = [text.index(heading) for heading in OUTLINE_HEADINGS]
    assert positions == sorted(positions)
    assert SELECTED_WORKED_CASE_SENTENCE in text

    for index, heading in enumerate(OUTLINE_HEADINGS):
        start = positions[index]
        end = positions[index + 1] if index + 1 < len(positions) else len(text)
        section = text[start:end]
        assert "reports/canonical/" in section, heading
        assert re.search(r"`\$", section), heading


def test_v1_report_pointers_resolve():
    failures: list[str] = []
    for path in V1_DOC_SURFACES:
        text = path.read_text(encoding="utf-8")
        for json_span, pointer in _extract_canonical_pointer_refs(text):
            json_path = _canonical_json_path(json_span)
            if json_path is None:
                failures.append(f"{path.relative_to(ROOT)}: unresolved JSON artifact {json_span}")
                continue
            if not json_path.exists():
                failures.append(f"{path.relative_to(ROOT)}: missing {json_span}")
                continue
            payload = json.loads(json_path.read_text(encoding="utf-8"))
            if not jsonpath_exists(payload, pointer):
                failures.append(f"{path.relative_to(ROOT)}: missing {json_span}:{pointer}")
    assert failures == []


def test_v1_docs_point_to_literature_ledger_without_listing_records():
    combined = "\n".join(path.read_text(encoding="utf-8") for path in V1_DOC_SURFACES)
    ledger = validate_literature_ledger(ROOT)

    assert "reports/canonical/index.json" in combined
    assert "$.literature_ledger" in combined
    assert ledger["status"] == "ready"
    for record_id in ledger["record_ids"]:
        assert record_id not in combined


def test_literature_ledger_gate_fails_when_docs_omit_index_pointer():
    result = check_literature_ledger({V1_REPORT: "literature ledger"}, MINIMAL_LEDGER_INDEX)

    assert result.status == "FAIL"
    assert "v1 docs must point to reports/canonical/index.json:$.literature_ledger" in result.detail


def test_literature_ledger_gate_fails_when_docs_repeat_record_id():
    ledger = validate_literature_ledger(ROOT)
    assert ledger["record_ids"]
    docs = {
        V1_REPORT: (
            "`reports/canonical/index.json:$.literature_ledger`\n"
            f"{ledger['record_ids'][0]}"
        )
    }

    result = check_literature_ledger(docs, MINIMAL_LEDGER_INDEX)

    assert result.status == "FAIL"
    assert f"v1 docs repeat literature ledger record id: {ledger['record_ids'][0]}" in result.detail


def test_literature_ledger_gate_fails_when_index_omits_ledger_entry():
    result = check_literature_ledger(MINIMAL_LEDGER_DOCS, {})

    assert result.status == "FAIL"
    assert "canonical index missing $.literature_ledger" in result.detail


def test_literature_ledger_gate_fails_when_index_ready_but_validator_not_ready(tmp_path, monkeypatch):
    import scripts.check_v1_report_docs as docs_gate

    monkeypatch.setattr(docs_gate, "ROOT", tmp_path)
    monkeypatch.setattr(docs_gate, "LITERATURE_LEDGER_PATH", tmp_path / "docs" / "lit" / "literature_ledger.yaml")

    result = docs_gate.check_literature_ledger(MINIMAL_LEDGER_DOCS, MINIMAL_LEDGER_INDEX)

    assert result.status == "FAIL"
    assert "canonical index claims ready while literature validator is not ready" in result.detail


def test_v1_report_uses_claim_terms_source():
    assert FORBIDDEN_POSITIVE_CLAIM_TERMS
    for path in V1_DOC_SURFACES:
        text = path.read_text(encoding="utf-8").lower()
        hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
        assert hits == [], f"{path.relative_to(ROOT)} contains forbidden positive claim terms: {hits}"


def test_v1_report_has_no_hidden_score_or_weight():
    for path in V1_DOC_SURFACES:
        text = path.read_text(encoding="utf-8").lower()
        hits = [term for term in HIDDEN_SCORECARD_TERMS if term in text]
        assert hits == [], f"{path.relative_to(ROOT)} contains hidden score/weight terms: {hits}"


def test_v1_report_has_no_gate_or_unique_positive_contract():
    assert not (CANONICAL / "v1-report-gate.json").exists()
    assert all(spec.json_artifact != "reports/canonical/v1-report-gate.json" for spec in canonical.CANONICAL_REPORTS)

    discovery_rows = json.loads((CANONICAL / "discovery_map.json").read_text(encoding="utf-8"))["rows"]
    rows_by_report = {row["report"]: row for row in discovery_rows}
    assert rows_by_report["gap-head-on-h"]["discovery_level"] == SELECTED_WORKED_CASE_DISCOVERY_LEVEL
    assert rows_by_report["gap-head-discovery"]["discovery_level"] == D4_DISCOVERY_LEVEL

    for path in V1_DOC_SURFACES:
        text = path.read_text(encoding="utf-8")
        hits = exclusive_positive_worked_case_hits({path: text})
        assert hits == [], path.relative_to(ROOT)


def test_v1_report_pointer_resolver_matches_hardgate_shorthand():
    payload = json.loads((CANONICAL / "discovery_map.json").read_text(encoding="utf-8"))
    assert jsonpath_exists(payload, "$.rows[report=gap-head-on-h].report")
    assert jsonpath_exists(payload, "$.rows[report=gap-head-discovery].discovery_level")


def test_v1_report_rejects_equivalent_unique_positive_wording():
    cases = [
        "gap-head-on-h is the only D4 row",
        "gap-head-on-h is the only D5 row",
        "gap-head-on-h is the sole positive row",
        "gap-head-on-h alone is D4",
        "gap-head-on-h alone is D5",
        "gap-head-on-h is the single discovery report",
        "gap-head-on-h is 唯一 D4",
        "gap-head-on-h is 唯一 D5",
        "gap-head-on-h 是唯一正",
    ]
    for phrase in cases:
        hits = exclusive_positive_worked_case_hits({V1_REPORT: phrase})
        assert hits != [], phrase


def test_v1_doc_hg_cli_wrapper_delegates_shared_scan(tmp_path, monkeypatch):
    import scripts.check_v1_report_docs as docs_gate

    path = tmp_path / "reports/canonical/dgt-l1-boundary-report.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_phrase("组件因果", "已全部证明\n"), encoding="utf-8")
    monkeypatch.setattr(docs_gate, "ROOT", tmp_path)
    monkeypatch.setattr(docs_gate, "DOC_PATHS", [path])

    result = check_doc_hg_surfaces()

    assert result.status == "FAIL"
    assert "DOC-HG forbidden phrase" in result.detail


def test_v1_doc_hg_cli_wrapper_accepts_boundary_pointer(tmp_path, monkeypatch):
    import scripts.check_v1_report_docs as docs_gate

    path = tmp_path / "reports/canonical/model-comparison.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "Boundary pointer: `reports/canonical/index.json:$.honest_boundary.not_claimed`\n"
        + _phrase("separation", "-persists\n"),
        encoding="utf-8",
    )
    monkeypatch.setattr(docs_gate, "ROOT", tmp_path)
    monkeypatch.setattr(docs_gate, "DOC_PATHS", [path])

    result = check_doc_hg_surfaces()

    assert result.status == "PASS"

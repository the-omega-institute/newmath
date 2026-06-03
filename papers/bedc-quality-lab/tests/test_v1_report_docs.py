import json
import re
from pathlib import Path

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
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
    "claim uniqueness among positive rows."
)
JSONPATH_RE = re.compile(
    r"^\$(?:\.[A-Za-z0-9_\-]+(?:\[(?:\*|\d+|[A-Za-z0-9_\-]+=[A-Za-z0-9_\-]+|\?\(@\.[A-Za-z0-9_\-]+==\"[^\"]+\"\))\])*)+$"
)
CANONICAL_JSON_RE = re.compile(r"^reports/canonical/[^`\s]+\.json$")
CANONICAL_JSON_WITH_POINTER_RE = re.compile(r"^(reports/canonical/[^`\s]+\.json):(\$.*)$")
CANONICAL_JSON_PAIR_RE = re.compile(r"^reports/canonical/([^`\s]+)\.\{json,md\}$")
CANONICAL_JSON_GLOB_RE = re.compile(r"^reports/canonical/\*\.\{json,md\}$")
FILTER_RE = re.compile(r"^\?\(@\.([A-Za-z0-9_\-]+)==\"([^\"]+)\"\)$")
ROW_FILTER_RE = re.compile(r"^([A-Za-z0-9_\-]+)=([A-Za-z0-9_\-]+)$")
UNIQUE_POSITIVE_RE = re.compile(r"\b(?:only|unique)\s+positive\b", re.IGNORECASE)


def _code_spans(text: str) -> list[str]:
    return re.findall(r"`([^`]+)`", text)


def _split_jsonpath(path: str) -> list[str]:
    segments: list[str] = []
    current: list[str] = []
    bracket_depth = 0
    for char in path:
        if char == "." and bracket_depth == 0:
            segments.append("".join(current))
            current = []
            continue
        if char == "[":
            bracket_depth += 1
        elif char == "]" and bracket_depth > 0:
            bracket_depth -= 1
        current.append(char)
    segments.append("".join(current))
    return segments


def _jsonpath_exists(data: object, pointer: str) -> bool:
    nodes = [data]
    for segment in _split_jsonpath(pointer[2:]):
        if not segment:
            return False
        key_match = re.match(r"^([A-Za-z0-9_\-]+)", segment)
        if key_match:
            key = key_match.group(1)
            nodes = [node[key] for node in nodes if isinstance(node, dict) and key in node]
            selector_part = segment[len(key) :]
        else:
            selector_part = segment
        if not nodes:
            return False
        for selector in re.findall(r"\[([^\]]+)\]", selector_part):
            next_nodes: list[object] = []
            if selector == "*":
                for node in nodes:
                    if isinstance(node, list):
                        next_nodes.extend(node)
            elif selector.isdigit():
                index = int(selector)
                for node in nodes:
                    if isinstance(node, list) and index < len(node):
                        next_nodes.append(node[index])
            elif filter_match := FILTER_RE.match(selector):
                field, expected = filter_match.groups()
                for node in nodes:
                    if isinstance(node, list):
                        next_nodes.extend(
                            item
                            for item in node
                            if isinstance(item, dict) and item.get(field) == expected
                        )
            elif row_match := ROW_FILTER_RE.match(selector):
                field, expected = row_match.groups()
                for node in nodes:
                    if isinstance(node, list):
                        next_nodes.extend(
                            item
                            for item in node
                            if isinstance(item, dict) and item.get(field) == expected
                        )
            else:
                return False
            nodes = next_nodes
            if not nodes:
                return False
    return bool(nodes)


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
            if current_json is not None and JSONPATH_RE.match(pointer):
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
            if not _jsonpath_exists(payload, pointer):
                failures.append(f"{path.relative_to(ROOT)}: missing {json_span}:{pointer}")
    assert failures == []


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
    assert rows_by_report["gap-head-on-h"]["discovery_level"] == "D4"
    assert rows_by_report["gap-head-discovery"]["discovery_level"] == "D4"

    for path in V1_DOC_SURFACES:
        text = path.read_text(encoding="utf-8")
        assert UNIQUE_POSITIVE_RE.search(text) is None, path.relative_to(ROOT)

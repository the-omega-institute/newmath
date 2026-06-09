#!/usr/bin/env python3
"""Read-only hardgate for v1 report outline documentation."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

if str(Path(__file__).resolve().parents[1]) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.literature_ledger import (
    FORBIDDEN_POSITIVE_CLAIM_TERMS as LITERATURE_FORBIDDEN_TERMS,
    LEDGER_POINTER,
    validate_literature_ledger,
)


ROOT = Path(__file__).resolve().parents[1]
DOC_PATHS = [
    ROOT / "docs" / "bedc_quality_lab_v1.md",
    ROOT / "docs" / "v1_report_outline.md",
    ROOT / "docs" / "bedc_quality_lab_alpha_milestone.md",
    ROOT / "docs" / "claims_and_nonclaims.md",
    ROOT / "docs" / "artifact_manifest.md",
]
INDEX_PATH = ROOT / "reports" / "canonical" / "index.json"
DISCOVERY_MAP_PATH = ROOT / "reports" / "canonical" / "discovery_map.json"
LITERATURE_LEDGER_PATH = ROOT / LEDGER_POINTER

BEDC_BODY_MARKERS = [
    r"\\closurestatus",
    r"\\begin\{closurestatus\}",
    r"\\origin\{",
    r"\\leanchecked",
    r"\\leanvariant",
    r"\\leansorryd",
    r"\\leanstmt",
    r"\\leandef",
    r"\\theoryclosure",
    r"\\scopeclosed",
    r"\\formalstatus",
    r"\\leantarget",
    r"\\bridgestatus",
    r"\\notclaimed",
    r"\\upgradepath",
]

SELECTED_WORKED_CASE_PHRASE = "selected positive worked case"
SELECTED_WORKED_CASE_REPORT = "gap-head-on-h"
D4_DISCOVERY_LEVEL = "D4"
SELECTED_WORKED_CASE_DISCOVERY_LEVEL = "D4"
POSITIVE_DISCOVERY_LEVELS = frozenset({"D4", "D5-O", "D5-M"})
NON_POSITIVE_REPORTS = [
    "certificate-guided-training",
    "certificate-guided-discovery",
    "nongaussian-distribution-sweep",
]
EXCLUSIVE_SELECTED_WORKED_CASE_RE = re.compile(
    r"(?:"
    r"\b(?:only|unique|sole|single)\s+(?:positive|d[45]|discovery)(?:\s+(?:row|report|case|artifact|finding|signal))?\b"
    r"|"
    r"\b(?:only|unique|sole|single)\s+(?:positive|d[45])\s+discovery\b"
    r"|"
    r"\bgap-head-on-h\s+(?:alone|is\s+(?:the\s+)?(?:only|unique|sole|single)\s+(?:positive|d[45]|discovery))\b"
    r"|"
    r"\bgap-head-on-h\s+alone\s+is\s+d[45]\b"
    r"|"
    r"\bthe\s+only\s+d[45]\b"
    r"|"
    r"唯一\s*(?:d[45]|正|正向|阳性|positive|discovery|发现)"
    r")",
    re.IGNORECASE,
)
POSITIVE_FRAMING_RE = re.compile(
    r"\bpositive\s+(?:result|discovery|prototype|finding|claim|outcome|artifact|report|signal)\b",
    re.IGNORECASE,
)
NEGATION_RE = re.compile(r"\b(?:not|never|no\s+longer|is\s+not|are\s+not|was\s+not|were\s+not)\b", re.IGNORECASE)

# Threat model: these hardgates are pointer-only thin-doc drift gates. They catch
# accidental report status flips, stale pointers, missing nonclaims, obvious
# positive framing of named artifacts, and simple negation tricks. They are not
# adversarial natural-language verifiers and do not defend arbitrary crafted
# prose; airtight adversarial coverage belongs to design-consensus work, not this
# thin-doc gate.


@dataclass
class CheckResult:
    name: str
    status: str
    detail: str


def read_docs() -> dict[Path, str]:
    docs: dict[Path, str] = {}
    missing = [path for path in DOC_PATHS if not path.exists()]
    if missing:
        names = ", ".join(str(path.relative_to(ROOT)) for path in missing)
        raise FileNotFoundError(f"missing doc file(s): {names}")
    for path in DOC_PATHS:
        docs[path] = path.read_text(encoding="utf-8")
    return docs


def load_index() -> tuple[dict | None, str]:
    if not INDEX_PATH.exists():
        return None, "missing canonical index"
    data = json.loads(INDEX_PATH.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("canonical index root must be a JSON object")
    return data, "canonical index loaded"


def iter_reports(index: dict) -> list[dict]:
    reports = index.get("reports")
    if not isinstance(reports, list):
        raise ValueError("canonical index missing list field $.reports")
    bad = [idx for idx, item in enumerate(reports) if not isinstance(item, dict)]
    if bad:
        raise ValueError(f"canonical index $.reports contains non-object entries: {bad}")
    return reports


def check_core_reports_pass(index: dict | None) -> CheckResult:
    if index is None:
        return CheckResult(
            "HG-V1-Report-1",
            "FAIL",
            "reports/canonical/index.json is missing",
        )
    reports = iter_reports(index)
    failing = [
        report.get("name", "<unnamed>")
        for report in reports
        if report.get("bundle_role") == "hg_p_core" and report.get("status") != "pass"
    ]
    if failing:
        return CheckResult(
            "HG-V1-Report-1",
            "FAIL",
            "hg_p_core report(s) not pass: " + ", ".join(failing),
        )
    return CheckResult("HG-V1-Report-1", "PASS", "all hg_p_core reports have status pass")


def check_required_nonclaims(docs: dict[Path, str]) -> CheckResult:
    text = docs[ROOT / "docs" / "claims_and_nonclaims.md"]
    if "reports/canonical/index.json:$.claims_nonclaims" not in text:
        return CheckResult(
            "HG-V1-Report-2",
            "FAIL",
            "claims boundary does not point to reports/canonical/index.json:$.claims_nonclaims",
        )
    index, _ = load_index()
    if index is None:
        return CheckResult("HG-V1-Report-2", "FAIL", "reports/canonical/index.json is missing")
    claims_nonclaims = index.get("claims_nonclaims")
    if not isinstance(claims_nonclaims, dict):
        return CheckResult("HG-V1-Report-2", "FAIL", "canonical index missing $.claims_nonclaims")
    items = claims_nonclaims.get("nonclaims")
    if not isinstance(items, list) or not items:
        return CheckResult("HG-V1-Report-2", "FAIL", "canonical index has no $.claims_nonclaims.nonclaims list")
    return CheckResult("HG-V1-Report-2", "PASS", "claims document points to canonical nonclaims")


def check_pointer_only_bedc(docs: dict[Path, str]) -> CheckResult:
    hits: list[str] = []
    for path, text in docs.items():
        for line_no, line in enumerate(text.splitlines(), start=1):
            for marker in BEDC_BODY_MARKERS:
                if re.search(marker, line):
                    hits.append(f"{path.relative_to(ROOT)}:{line_no}:{line.strip()}")
    if hits:
        return CheckResult(
            "HG-V1-Report-3",
            "FAIL",
            "BEDC body marker(s) found: " + " | ".join(hits),
        )
    return CheckResult("HG-V1-Report-3", "PASS", "no BEDC body-copy markers found")


def check_certificate_guided_boundary(docs: dict[Path, str]) -> CheckResult:
    training_lines = lines_with_phrase(docs, "certificate-guided-training")
    if not training_lines:
        return CheckResult("HG-V1-Report-4", "FAIL", "certificate-guided-training is not documented")
    positive_lines = [
        hit
        for hit in non_positive_positive_framing_hits(docs)
        if "certificate-guided-training" in hit.lower()
    ]
    if positive_lines:
        return CheckResult(
            "HG-V1-Report-4",
            "FAIL",
            "certificate-guided-training is framed with positive wording: "
            + " | ".join(positive_lines),
        )
    if not DISCOVERY_MAP_PATH.exists():
        return CheckResult("HG-V1-Report-4", "FAIL", "canonical discovery map is missing")
    payload = json.loads(DISCOVERY_MAP_PATH.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return CheckResult("HG-V1-Report-4", "FAIL", "canonical discovery map missing $.rows")
    training_rows = [
        row
        for row in rows
        if isinstance(row, dict) and row.get("report") == "certificate-guided-training"
    ]
    if not training_rows:
        return CheckResult("HG-V1-Report-4", "FAIL", "certificate-guided-training row missing from discovery map")
    if training_rows[0].get("discovery_level") == "D4":
        return CheckResult("HG-V1-Report-4", "FAIL", "certificate-guided-training is D4 in discovery map")
    return CheckResult("HG-V1-Report-4", "PASS", "certificate-guided-training boundary is canonical-map owned")


def lines_with_phrase(docs: dict[Path, str], phrase: str) -> list[str]:
    hits: list[str] = []
    phrase_lower = phrase.lower()
    for path, text in docs.items():
        for line_no, line in enumerate(text.splitlines(), start=1):
            if phrase_lower in line.lower():
                hits.append(f"{path.relative_to(ROOT)}:{line_no}:{line.strip()}")
    return hits


def has_positive_framing(hit: str) -> bool:
    return bool(POSITIVE_FRAMING_RE.search(hit))


def has_simple_negation(hit: str) -> bool:
    return bool(NEGATION_RE.search(hit))


def non_positive_positive_framing_hits(docs: dict[Path, str]) -> list[str]:
    hits: list[str] = []
    for path, text in docs.items():
        for line_no, line in enumerate(text.splitlines(), start=1):
            lowered = line.lower()
            mentioned = [name for name in NON_POSITIVE_REPORTS if name in lowered]
            if not mentioned:
                continue
            if not has_positive_framing(line) or has_simple_negation(line):
                continue
            names = ",".join(mentioned)
            hits.append(f"{path.relative_to(ROOT)}:{line_no}:{names}:{line.strip()}")
    return hits


def check_selected_positive_worked_case(docs: dict[Path, str]) -> CheckResult:
    hidden_unique_hits = exclusive_positive_worked_case_hits(docs)
    if hidden_unique_hits:
        return CheckResult(
            "HG-V1-Report-5",
            "FAIL",
            "exclusive positive wording found: " + " | ".join(hidden_unique_hits),
        )

    selected_hits = [
        hit
        for hit in lines_with_phrase(docs, SELECTED_WORKED_CASE_PHRASE)
        if SELECTED_WORKED_CASE_REPORT in hit and not has_simple_negation(hit)
    ]
    if not selected_hits:
        return CheckResult(
            "HG-V1-Report-5",
            "FAIL",
            "gap-head-on-h is not named as the selected positive worked case",
        )

    if not DISCOVERY_MAP_PATH.exists():
        return CheckResult("HG-V1-Report-5", "FAIL", "canonical discovery map is missing")
    payload = json.loads(DISCOVERY_MAP_PATH.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return CheckResult("HG-V1-Report-5", "FAIL", "canonical discovery map missing $.rows")
    selected_rows = [
        row
        for row in rows
        if isinstance(row, dict) and row.get("report") == SELECTED_WORKED_CASE_REPORT
    ]
    if not selected_rows:
        return CheckResult("HG-V1-Report-5", "FAIL", "gap-head-on-h row missing from discovery map")
    if selected_rows[0].get("discovery_level") != SELECTED_WORKED_CASE_DISCOVERY_LEVEL:
        return CheckResult(
            "HG-V1-Report-5",
            "FAIL",
            f"gap-head-on-h is not {SELECTED_WORKED_CASE_DISCOVERY_LEVEL} in discovery map",
        )
    return CheckResult("HG-V1-Report-5", "PASS", "gap-head-on-h is the selected positive worked case")


def exclusive_positive_worked_case_hits(docs: dict[Path, str]) -> list[str]:
    if positive_discovery_report_count() < 2:
        return []
    hits: list[str] = []
    for path, text in docs.items():
        for line_no, line in enumerate(text.splitlines(), start=1):
            if EXCLUSIVE_SELECTED_WORKED_CASE_RE.search(line):
                hits.append(f"{path.relative_to(ROOT)}:{line_no}:{line.strip()}")
    return hits


def positive_discovery_report_count() -> int:
    if not DISCOVERY_MAP_PATH.exists():
        return 0
    payload = json.loads(DISCOVERY_MAP_PATH.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return 0
    return sum(
        1
        for row in rows
        if isinstance(row, dict) and row.get("discovery_level") in POSITIVE_DISCOVERY_LEVELS
    )


REPORT_REF_RE = re.compile(r"^reports/canonical/([^`\s]+)$")
FILTER_RE = re.compile(r"^\?\(@\.([A-Za-z0-9_\-]+)==\"([^\"]+)\"\)$")
ROW_FILTER_RE = re.compile(r"^([A-Za-z0-9_\-]+)=([A-Za-z0-9_\-]+)$")
JSONPATH_SELECTOR_RE = r"(?:\*|\d+|[A-Za-z0-9_\-]+=[A-Za-z0-9_\-]+|\?\(@\.[A-Za-z0-9_\-]+==\"[^\"]+\"\))"
JSON_POINTER_RE = re.compile(
    rf"^\$(?:\.[A-Za-z0-9_\-]+(?:\[{JSONPATH_SELECTOR_RE}\])*)+$"
)


def check_json_pointers(docs: dict[Path, str]) -> CheckResult:
    failures: list[str] = []
    for path, text in docs.items():
        current_json: Path | None = None
        for line_no, line in enumerate(text.splitlines(), start=1):
            code_spans = re.findall(r"`([^`]+)`", line)
            line_has_pointer = any(JSON_POINTER_RE.match(span.rstrip(".,;:")) for span in code_spans)
            path_line = line.lstrip().startswith("- Path:")
            for code_span in code_spans:
                report_path = json_report_path_from_span(code_span)
                if report_path is not None:
                    if line_has_pointer or path_line:
                        current_json = report_path
                    continue
                pointer = code_span.rstrip(".,;:")
                if not JSON_POINTER_RE.match(pointer):
                    continue
                if current_json is None:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line_no}:{pointer} has no preceding canonical JSON artifact"
                    )
                    continue
                if not current_json.exists():
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line_no}:{current_json.relative_to(ROOT)} does not exist"
                    )
                    continue
                try:
                    data = json.loads(current_json.read_text(encoding="utf-8"))
                except Exception as exc:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line_no}:{current_json.relative_to(ROOT)} is unreadable: {exc}"
                    )
                    continue
                if not jsonpath_exists(data, pointer):
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line_no}:{current_json.relative_to(ROOT)} {pointer} is missing"
                    )
    if failures:
        return CheckResult(
            "HG-V1-Report-pointers",
            "FAIL",
            "invalid JSON pointer(s): " + " | ".join(failures),
        )
    return CheckResult("HG-V1-Report-pointers", "PASS", "all canonical JSON pointers resolve")


def check_literature_ledger(docs: dict[Path, str], index: dict | None) -> CheckResult:
    summary = validate_literature_ledger(ROOT)
    failures = list(summary["failures"])
    combined_docs = "\n".join(docs.values())
    if "reports/canonical/index.json" not in combined_docs or "$.literature_ledger" not in combined_docs:
        failures.append("v1 docs must point to reports/canonical/index.json:$.literature_ledger")

    for record_id in summary["record_ids"]:
        if record_id in combined_docs:
            failures.append(f"v1 docs repeat literature ledger record id: {record_id}")

    if LITERATURE_LEDGER_PATH.exists():
        ledger_text = LITERATURE_LEDGER_PATH.read_text(encoding="utf-8").lower()
        for term in LITERATURE_FORBIDDEN_TERMS:
            if term in ledger_text:
                failures.append(f"literature ledger contains forbidden wording: {term}")

    if index is None:
        failures.append("reports/canonical/index.json is missing")
    else:
        index_ledger = index.get("literature_ledger")
        if not isinstance(index_ledger, dict):
            failures.append("canonical index missing $.literature_ledger")
        elif index_ledger.get("status") == "ready" and summary["status"] != "ready":
            failures.append("canonical index claims ready while literature validator is not ready")

    if failures:
        return CheckResult(
            "HG-V1-Report-literature-ledger",
            "FAIL",
            " | ".join(failures),
        )
    return CheckResult(
        "HG-V1-Report-literature-ledger",
        "PASS",
        "literature ledger readiness is validator-owned and docs stay pointer-only",
    )


def json_report_path_from_span(span: str) -> Path | None:
    match = REPORT_REF_RE.match(span)
    if not match:
        return None
    suffix = match.group(1)
    if suffix == "*.{json,md}":
        return None
    if suffix.endswith(".json"):
        return ROOT / "reports" / "canonical" / suffix
    if suffix.endswith(".{json,md}"):
        return ROOT / "reports" / "canonical" / (suffix.removesuffix(".{json,md}") + ".json")
    return None


def jsonpath_exists(data: object, pointer: str) -> bool:
    nodes = [data]
    for segment in split_jsonpath(pointer[2:]):
        if not segment:
            return False
        key_match = re.match(r"^([A-Za-z0-9_\-]+)", segment)
        if key_match:
            key = key_match.group(1)
            nodes = [node[key] for node in nodes if isinstance(node, dict) and key in node]
            selector_part = segment[len(key):]
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
            else:
                filter_match = FILTER_RE.match(selector)
                if filter_match:
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


def split_jsonpath(path: str) -> list[str]:
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


def main() -> int:
    try:
        docs = read_docs()
        index, index_detail = load_index()
        results = [
            check_core_reports_pass(index),
            check_required_nonclaims(docs),
            check_pointer_only_bedc(docs),
            check_certificate_guided_boundary(docs),
            check_selected_positive_worked_case(docs),
            check_json_pointers(docs),
            check_literature_ledger(docs, index),
        ]
    except Exception as exc:
        print(f"HG-V1-Report-DOCS: FAIL: {exc}")
        return 1

    print(f"HG-V1-Report-index: {index_detail}")
    for result in results:
        print(f"{result.name}: {result.status}: {result.detail}")
    if any(result.status == "FAIL" for result in results):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

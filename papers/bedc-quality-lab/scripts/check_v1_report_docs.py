#!/usr/bin/env python3
"""Read-only hardgate for v1 report outline documentation."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOC_PATHS = [
    ROOT / "docs" / "v1_report_outline.md",
    ROOT / "docs" / "claims_and_nonclaims.md",
    ROOT / "docs" / "artifact_manifest.md",
]
INDEX_PATH = ROOT / "reports" / "canonical" / "index.json"

REQUIRED_NONCLAIMS = [
    "not full LeJEPA",
    "not full Tensor NameCert",
    "not global quality",
    "not LLM behavior",
    "not solved model quality",
]

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

POSITIVE_PROTOTYPE_PHRASE = "positive discovery prototype"
UNIQUE_POSITIVE_REPORT = "gap-head-on-h"
NON_POSITIVE_REPORTS = [
    "gap-head-discovery",
    "certificate-guided-training",
    "certificate-guided-discovery",
    "nongaussian-distribution-sweep",
]


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
        return None, "missing canonical index; index-dependent checks skipped"
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
            "SKIP",
            "reports/canonical/index.json is missing; no pass claim made",
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
    missing = [item for item in REQUIRED_NONCLAIMS if item not in text]
    if missing:
        return CheckResult("HG-V1-Report-2", "FAIL", "missing exact nonclaim(s): " + ", ".join(missing))
    return CheckResult("HG-V1-Report-2", "PASS", "all exact nonclaims present")


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
    text = "\n".join(docs.values()).lower()
    if "certificate-guided-training" not in text:
        return CheckResult("HG-V1-Report-4", "FAIL", "certificate-guided-training is not documented")
    if "certificate-guided-training" in text and "mixed/negative" not in text:
        return CheckResult("HG-V1-Report-4", "FAIL", "certificate-guided-training lacks mixed/negative label")
    bad_patterns = [
        r"certificate-guided-training[^\n.]*positive discovery prototype",
        r"positive discovery prototype[^\n.]*certificate-guided-training",
    ]
    for pattern in bad_patterns:
        if re.search(pattern, text):
            return CheckResult(
                "HG-V1-Report-4",
                "FAIL",
                "certificate-guided-training is framed with positive prototype wording",
            )
    return CheckResult("HG-V1-Report-4", "PASS", "certificate-guided-training is mixed/negative")


def lines_with_phrase(docs: dict[Path, str], phrase: str) -> list[str]:
    hits: list[str] = []
    phrase_lower = phrase.lower()
    for path, text in docs.items():
        for line_no, line in enumerate(text.splitlines(), start=1):
            if phrase_lower in line.lower():
                hits.append(f"{path.relative_to(ROOT)}:{line_no}:{line.strip()}")
    return hits


def check_unique_positive_prototype(docs: dict[Path, str]) -> CheckResult:
    hits = lines_with_phrase(docs, POSITIVE_PROTOTYPE_PHRASE)
    bad_hits = [hit for hit in hits if UNIQUE_POSITIVE_REPORT not in hit]
    non_positive_bad: list[str] = []
    for hit in hits:
        lowered = hit.lower()
        for name in NON_POSITIVE_REPORTS:
            if name in lowered and UNIQUE_POSITIVE_REPORT not in lowered:
                non_positive_bad.append(hit)
    if bad_hits or non_positive_bad:
        details = bad_hits + non_positive_bad
        return CheckResult(
            "HG-V1-Report-5",
            "FAIL",
            "positive prototype wording outside gap-head-on-h: " + " | ".join(details),
        )
    all_text = "\n".join(docs.values())
    if UNIQUE_POSITIVE_REPORT not in all_text or POSITIVE_PROTOTYPE_PHRASE not in all_text:
        return CheckResult(
            "HG-V1-Report-5",
            "FAIL",
            "gap-head-on-h is not marked as the positive discovery prototype",
        )
    return CheckResult("HG-V1-Report-5", "PASS", "gap-head-on-h is the unique positive prototype")


def main() -> int:
    try:
        docs = read_docs()
        index, index_detail = load_index()
        results = [
            check_core_reports_pass(index),
            check_required_nonclaims(docs),
            check_pointer_only_bedc(docs),
            check_certificate_guided_boundary(docs),
            check_unique_positive_prototype(docs),
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

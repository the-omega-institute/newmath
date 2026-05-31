#!/usr/bin/env python3
import json
import sys
import tempfile
from pathlib import Path

import bedc_ci


PLAN = "Replace this statement-only paper site with a checked Lean target or an explicit setup-field contract."


def marker(file: str, target: str, line: int = 1) -> bedc_ci.LeanMarkerRecord:
    return bedc_ci.LeanMarkerRecord(file=file, line=line, macro="leanstmt", target=target)


def entry(file: str, target: str, line: int | None = None, plan: str = PLAN) -> bedc_ci.LeanStmtDebtEntry:
    return bedc_ci.LeanStmtDebtEntry(file=file, target=target, discharge_plan=plan, line=line)


def violation_kinds(payload: dict[str, object]) -> set[str]:
    return {str(item["kind"]) for item in payload["violations"]}


def check_clean_registered_sites() -> None:
    payload = bedc_ci.leanstmt_debt_payload(
        [marker("parts/a.tex", "BEDC.A", 5)],
        [entry("parts/a.tex", "BEDC.A", 5)],
    )
    assert payload["violations"] == []


def check_unregistered_live_site() -> None:
    payload = bedc_ci.leanstmt_debt_payload(
        [marker("parts/a.tex", "BEDC.A", 5)],
        [],
    )
    assert violation_kinds(payload) == {"unregistered_live_site"}


def check_stale_manifest_entry() -> None:
    payload = bedc_ci.leanstmt_debt_payload(
        [],
        [entry("parts/a.tex", "BEDC.A", 5)],
    )
    assert violation_kinds(payload) == {"stale_manifest_entry"}


def check_blank_or_placeholder_plan() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps({
            "schema": "leanstmt_debt_manifest.v1",
            "entries": [
                {
                    "file": "parts/a.tex",
                    "target": "BEDC.A",
                    "discharge_plan": "TODO",
                },
                {
                    "file": "parts/b.tex",
                    "target": "BEDC.B",
                    "discharge_plan": "   ",
                },
            ],
        }), encoding="utf-8")
        entries, diagnostics = bedc_ci.load_leanstmt_debt_manifest(path)
    assert len(entries) == 2
    assert [item["kind"] for item in diagnostics] == [
        "manifest_entry_invalid_discharge_plan",
        "manifest_entry_invalid_discharge_plan",
    ]


def check_missing_required_fields() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps({
            "schema": "leanstmt_debt_manifest.v1",
            "entries": [
                {"file": "parts/a.tex", "discharge_plan": PLAN},
                {"target": "BEDC.B", "discharge_plan": PLAN},
                {"file": "parts/c.tex", "target": "BEDC.C"},
            ],
        }), encoding="utf-8")
        _, diagnostics = bedc_ci.load_leanstmt_debt_manifest(path)
    kinds = [str(item["kind"]) for item in diagnostics]
    assert kinds.count("manifest_entry_missing_keys") == 3
    assert "manifest_entry_invalid_target" in kinds
    assert "manifest_entry_invalid_file" in kinds
    assert "manifest_entry_invalid_discharge_plan" in kinds


def check_duplicate_manifest_key() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps({
            "schema": "leanstmt_debt_manifest.v1",
            "entries": [
                {
                    "file": "parts/a.tex",
                    "target": "BEDC.A",
                    "discharge_plan": PLAN,
                },
                {
                    "file": "parts/a.tex",
                    "target": "BEDC.A",
                    "discharge_plan": PLAN,
                },
            ],
        }), encoding="utf-8")
        _, diagnostics = bedc_ci.load_leanstmt_debt_manifest(path)
    assert "manifest_duplicate_key" in {str(item["kind"]) for item in diagnostics}


def check_duplicate_same_file_live_key() -> None:
    payload = bedc_ci.leanstmt_debt_payload(
        [
            marker("parts/a.tex", "BEDC.A", 5),
            marker("parts/a.tex", "BEDC.A", 9),
        ],
        [entry("parts/a.tex", "BEDC.A", 5)],
    )
    assert "duplicate_live_site" in violation_kinds(payload)


def check_same_target_in_different_files_require_separate_entries() -> None:
    one_entry_payload = bedc_ci.leanstmt_debt_payload(
        [
            marker("parts/a.tex", "BEDC.Shared", 5),
            marker("parts/b.tex", "BEDC.Shared", 7),
        ],
        [entry("parts/a.tex", "BEDC.Shared", 5)],
    )
    assert violation_kinds(one_entry_payload) == {"unregistered_live_site"}

    two_entry_payload = bedc_ci.leanstmt_debt_payload(
        [
            marker("parts/a.tex", "BEDC.Shared", 5),
            marker("parts/b.tex", "BEDC.Shared", 7),
        ],
        [
            entry("parts/a.tex", "BEDC.Shared", 5),
            entry("parts/b.tex", "BEDC.Shared", 7),
        ],
    )
    assert two_entry_payload["violations"] == []


def main() -> int:
    check_clean_registered_sites()
    check_unregistered_live_site()
    check_stale_manifest_entry()
    check_blank_or_placeholder_plan()
    check_missing_required_fields()
    check_duplicate_manifest_key()
    check_duplicate_same_file_live_key()
    check_same_target_in_different_files_require_separate_entries()
    print("OK: leanstmt debt clean registered sites")
    print("OK: leanstmt debt fail contracts")
    print("OK: leanstmt debt site keys")
    return 0


if __name__ == "__main__":
    sys.exit(main())

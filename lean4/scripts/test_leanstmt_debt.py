#!/usr/bin/env python3
import json
import sys
import tempfile
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from typing import Callable

import bedc_ci


PLAN = "Replace this statement-only paper site with a checked Lean target or an explicit setup-field contract."


def marker(file: str, target: str, line: int = 1) -> bedc_ci.LeanMarkerRecord:
    return bedc_ci.LeanMarkerRecord(file=file, line=line, macro="leanstmt", target=target)


def entry(file: str, target: str, plan: str = PLAN) -> bedc_ci.LeanStmtDebtEntry:
    return bedc_ci.LeanStmtDebtEntry(file=file, target=target, discharge_plan=plan)


def violation_kinds(payload: dict[str, object]) -> set[str]:
    return {str(item["kind"]) for item in payload["violations"]}


def check_clean_registered_sites() -> None:
    payload = bedc_ci.leanstmt_debt_payload(
        [marker("parts/a.tex", "BEDC.A", 5)],
        [entry("parts/a.tex", "BEDC.A")],
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
        [entry("parts/a.tex", "BEDC.A")],
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
        [entry("parts/a.tex", "BEDC.A")],
    )
    assert "duplicate_live_site" in violation_kinds(payload)


def check_same_target_in_different_files_require_separate_entries() -> None:
    one_entry_payload = bedc_ci.leanstmt_debt_payload(
        [
            marker("parts/a.tex", "BEDC.Shared", 5),
            marker("parts/b.tex", "BEDC.Shared", 7),
        ],
        [entry("parts/a.tex", "BEDC.Shared")],
    )
    assert violation_kinds(one_entry_payload) == {"unregistered_live_site"}

    two_entry_payload = bedc_ci.leanstmt_debt_payload(
        [
            marker("parts/a.tex", "BEDC.Shared", 5),
            marker("parts/b.tex", "BEDC.Shared", 7),
        ],
        [
            entry("parts/a.tex", "BEDC.Shared"),
            entry("parts/b.tex", "BEDC.Shared"),
        ],
    )
    assert two_entry_payload["violations"] == []


def manifest_diagnostics(raw: object) -> list[dict[str, object]]:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        if isinstance(raw, str):
            path.write_text(raw, encoding="utf-8")
        else:
            path.write_text(json.dumps(raw), encoding="utf-8")
        _, diagnostics = bedc_ci.load_leanstmt_debt_manifest(path)
    return diagnostics


def check_parser_branches() -> None:
    cases = [
        ("manifest_invalid_json", "{"),
        ("manifest_invalid_shape", []),
        ("manifest_extra_top_keys", {"schema": "leanstmt_debt_manifest.v1", "entries": [], "extra": True}),
        ("manifest_missing_top_keys", {"schema": "leanstmt_debt_manifest.v1"}),
        ("manifest_schema_mismatch", {"schema": "wrong", "entries": []}),
        ("manifest_entries_invalid", {"schema": "leanstmt_debt_manifest.v1", "entries": {}}),
        ("manifest_entry_invalid", {"schema": "leanstmt_debt_manifest.v1", "entries": [None]}),
        (
            "manifest_entry_extra_keys",
            {
                "schema": "leanstmt_debt_manifest.v1",
                "entries": [
                    {
                        "file": "parts/a.tex",
                        "target": "BEDC.A",
                        "discharge_plan": PLAN,
                        "line": 1,
                    }
                ],
            },
        ),
    ]
    for expected, raw in cases:
        kinds = {str(item["kind"]) for item in manifest_diagnostics(raw)}
        assert expected in kinds


def with_patch(patches: dict[str, object], fn: Callable[[], None]) -> None:
    originals = {name: getattr(bedc_ci, name) for name in patches}
    try:
        for name, value in patches.items():
            setattr(bedc_ci, name, value)
        fn()
    finally:
        for name, value in originals.items():
            setattr(bedc_ci, name, value)


def leanstmt_audit_result(
    manifest_loader: Callable[[], tuple[list[bedc_ci.LeanStmtDebtEntry], list[dict[str, object]]]],
    markers: list[bedc_ci.LeanMarkerRecord] | None = None,
) -> tuple[int, str]:
    patches = {
        "_get_commit_changed_files": lambda: set(),
        "build_declaration_inventory": lambda: ([], []),
        "collect_part_labels": lambda: [],
        "collect_lean_markers": lambda: list(markers or []),
        "load_leanstmt_debt_manifest": manifest_loader,
        "lean_files": lambda: [],
        "detect_case_collision_paths": lambda: [],
        "detect_preamble_duplicate_commands": lambda: [],
        "detect_concrete_instance_number_collisions": lambda: [],
        "detect_concrete_instance_missing_origin": lambda: [],
        "detect_paper_chapter_origin_tags": lambda: [],
        "collect_closurestatus_blocks": lambda _root: [],
        "detect_orphan_concrete_subdirs": lambda: [],
    }
    result: dict[str, object] = {}

    def run() -> None:
        out = StringIO()
        args = bedc_ci.argparse.Namespace(json=False, shape_saturation=False)
        with redirect_stdout(out):
            result["rc"] = bedc_ci.cmd_audit(args)
        result["text"] = out.getvalue()

    with_patch(patches, run)
    return int(result["rc"]), str(result["text"])


def check_audit_gate_rejects_missing_manifest() -> None:
    original_loader = bedc_ci.load_leanstmt_debt_manifest
    missing_path = bedc_ci.SCRIPT_DIR / "__missing_leanstmt_debt_manifest_for_test__.json"
    assert not missing_path.exists()

    def run() -> None:
        rc, text = leanstmt_audit_result(lambda: original_loader(missing_path))
        assert rc != 0
        assert "[bedc-ci] leanstmt debt:" in text
        assert "violations=1" in text
        assert "manifest_missing" in text

    with_patch({"LEANSTMT_DEBT_MANIFEST_PATH": missing_path}, run)


def check_audit_gate_rejects_missing_top_keys() -> None:
    original_loader = bedc_ci.load_leanstmt_debt_manifest
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps({"schema": "leanstmt_debt_manifest.v1"}), encoding="utf-8")
        rc, text = leanstmt_audit_result(lambda: original_loader(path))
    assert rc != 0
    assert "manifest_missing_top_keys" in text


def check_audit_gate_rejects_invalid_entry_shape() -> None:
    original_loader = bedc_ci.load_leanstmt_debt_manifest
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps({
            "schema": "leanstmt_debt_manifest.v1",
            "entries": [None],
        }), encoding="utf-8")
        rc, text = leanstmt_audit_result(lambda: original_loader(path))
    assert rc != 0
    assert "manifest_entry_invalid" in text


def check_audit_gate_rejects_unregistered_live_site() -> None:
    rc, text = leanstmt_audit_result(
        lambda: ([], []),
        [marker("parts/a.tex", "BEDC.A", 5)],
    )
    assert rc != 0
    assert "[bedc-ci] leanstmt debt:" in text
    assert "violations=1" in text
    assert "unregistered_live_site" in text


def main() -> int:
    check_clean_registered_sites()
    check_unregistered_live_site()
    check_stale_manifest_entry()
    check_blank_or_placeholder_plan()
    check_missing_required_fields()
    check_duplicate_manifest_key()
    check_duplicate_same_file_live_key()
    check_same_target_in_different_files_require_separate_entries()
    check_parser_branches()
    check_audit_gate_rejects_missing_manifest()
    check_audit_gate_rejects_missing_top_keys()
    check_audit_gate_rejects_invalid_entry_shape()
    check_audit_gate_rejects_unregistered_live_site()
    print("OK: leanstmt debt clean registered sites")
    print("OK: leanstmt debt fail contracts")
    print("OK: leanstmt debt site keys")
    print("OK: leanstmt debt parser and audit gate")
    return 0


if __name__ == "__main__":
    sys.exit(main())

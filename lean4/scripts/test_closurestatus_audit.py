"""Unit tests for the closurestatus block parser in bedc_ci.py."""
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import (  # type: ignore[import-not-found]
    CLOSURESTATUS_BEGIN_RE,
    CLOSURESTATUS_FIELD_RE,
    audit_payload,
    collect_closurestatus_blocks,
    diagnose_closurestatus_block,
    diagnose_closurestatus_open_fields,
)


class ClosurestatusRegexTests(unittest.TestCase):
    # Refactor (iter/issue-253):
    #   Old pattern: closurestatus 是固定字段协议;要承载更多审计属性会倾向引入版本号(\closureprofileversion{N}),但 3510 个 \begin{closurestatus} block 强制迁移不现实,也违反 CLAUDE.md 禁版本号。
    #   New principle: 开放可扩展审计记录:字段存在性决定能力,声明强度决定严格程度。共识=A-inline now(inline 宏 + bedc_ci 能力检测)+ 文档化 extraction trigger,不建首版 record 模块。
    def test_begin_regex_matches_simple_form(self) -> None:
        block = r"\begin{closurestatus}{\NatUp}"
        m = CLOSURESTATUS_BEGIN_RE.search(block)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "Nat")

    def test_field_regex_extracts_lean_target(self) -> None:
        body = r"\leantarget{BEDC.Foo.Bar\_baz}"
        m = CLOSURESTATUS_FIELD_RE.search(body)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "leantarget")
        self.assertEqual(m.group(2), r"BEDC.Foo.Bar\_baz")

    def test_field_regex_extracts_open_field(self) -> None:
        body = r"\closureclaimkind{discovery}"
        m = CLOSURESTATUS_FIELD_RE.search(body)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "closureclaimkind")
        self.assertEqual(m.group(2), "discovery")


class ClosurestatusDiagnosticsTests(unittest.TestCase):
    def _block(self, **overrides):
        base = {
            "file": "papers/bedc/parts/x.tex",
            "line": 1,
            "region": "Foo",
            "theory_closure": "scopedClosure",
            "formal_status": "theoremCheckedV",
            "lean_target": "BEDC.Foo.example",
            "bridge_status": "none",
            "has_scope": True,
            "has_notclaimed": True,
            "has_upgradepath": True,
            "has_constructive_story": True,
            "open_fields": {},
        }
        base.update(overrides)
        return base

    def test_clean_block_passes(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(), lean_symbols={"BEDC.Foo.example"}
        )
        self.assertEqual(diags, [])

    def test_invalid_theory_closure_grade_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(theory_closure="bogusGrade"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("invalid theoryclosure" in d for d in diags))

    def test_theorem_checked_without_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target=None),
            lean_symbols=set(),
        )
        self.assertTrue(any("requires \\leantarget" in d for d in diags))

    def test_unresolved_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target="BEDC.Missing.thing"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(
            any("does not resolve under lean4/BEDC" in d for d in diags)
        )

    def test_missing_scope_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(has_scope=False),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("missing \\scopeclosed" in d for d in diags))

    def test_legacy_block_has_no_open_field_lint(self) -> None:
        warnings, errors = diagnose_closurestatus_open_fields(self._block())
        self.assertEqual(warnings, [])
        self.assertEqual(errors, [])

    def test_weak_claim_missing_evidence_warns_only(self) -> None:
        warnings, errors = diagnose_closurestatus_open_fields(
            self._block(open_fields={"closureclaimkind": "survey"})
        )
        self.assertTrue(any("lacks \\closurenamecert" in item["message"] for item in warnings))
        self.assertEqual(errors, [])

    def test_strong_discovery_missing_evidence_errors(self) -> None:
        warnings, errors = diagnose_closurestatus_open_fields(
            self._block(open_fields={"closureclaimkind": "discovery"})
        )
        self.assertEqual(warnings, [])
        self.assertTrue(any("requires \\closurenamecert" in item["message"] for item in errors))
        self.assertTrue(any("requires \\closureledger" in item["message"] for item in errors))
        self.assertTrue(
            any("requires \\closureclassifierincrement" in item["message"] for item in errors)
        )

    def test_classifier_increment_must_be_one(self) -> None:
        warnings, errors = diagnose_closurestatus_open_fields(
            self._block(
                open_fields={
                    "closureclaimkind": "discovery",
                    "closurenamecert": "n",
                    "closureledger": "l",
                    "closureclassifierincrement": "2",
                }
            )
        )
        self.assertEqual(warnings, [])
        self.assertTrue(any("must be 1" in item["message"] for item in errors))

    def test_collect_blocks_preserves_open_fields(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td) / "papers" / "bedc" / "parts"
            root.mkdir(parents=True)
            (root / "x.tex").write_text(
                "\n".join(
                    [
                        r"\begin{closurestatus}{\FooUp}",
                        r"  \theoryclosure{\scopedClosure}",
                        r"  \formalstatus{\theoremCheckedV}",
                        r"  \leantarget{BEDC.Foo.example}",
                        r"  \scopeclosed{scope}",
                        r"  \notclaimed{none}",
                        r"  \upgradepath{done}",
                        r"  \constructivestory{}",
                        r"  \closureclaimkind{discovery}",
                        r"  \closurenamecert{NameCert row}",
                        r"\end{closurestatus}",
                    ]
                ),
                encoding="utf-8",
            )
            blocks = collect_closurestatus_blocks(root)
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0]["open_fields"]["closureclaimkind"], "discovery")
        self.assertEqual(blocks[0]["open_fields"]["closurenamecert"], "NameCert row")

    def test_audit_payload_exposes_open_warning_and_error_keys(self) -> None:
        block = self._block(open_fields={"closureclaimkind": "discovery"})
        with patch("bedc_ci._get_commit_changed_files", return_value=None), \
            patch("bedc_ci.build_declaration_inventory", return_value=([], [])), \
            patch("bedc_ci.collect_part_labels", return_value=[]), \
            patch("bedc_ci.collect_lean_markers", return_value=[]), \
            patch("bedc_ci.lean_files", return_value=[]), \
            patch("bedc_ci.detect_case_collision_paths", return_value=[]), \
            patch("bedc_ci.detect_preamble_duplicate_commands", return_value=[]), \
            patch("bedc_ci.detect_concrete_instance_number_collisions", return_value=[]), \
            patch("bedc_ci.detect_concrete_instance_missing_origin", return_value=[]), \
            patch("bedc_ci.detect_paper_chapter_origin_tags", return_value=[]), \
            patch("bedc_ci.collect_closurestatus_blocks", return_value=[block]), \
            patch("bedc_ci.detect_orphan_concrete_subdirs", return_value=[]):
            payload = audit_payload()
        self.assertIn("closurestatus_open_warnings", payload)
        self.assertIn("closurestatus_open_errors", payload)
        self.assertEqual(payload["closurestatus_open_warnings_count"], 0)
        self.assertGreater(payload["closurestatus_open_errors_count"], 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)

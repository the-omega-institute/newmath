"""Unit tests for the closurestatus block parser in bedc_ci.py."""
import sys
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import (  # type: ignore[import-not-found]
    CLOSURESTATUS_BEGIN_RE,
    CLOSURESTATUS_FIELD_RE,
    DiscoveryDeltaLedgerRecord,
    ExprFingerprint,
    LeanSourceScan,
    _discovery_candidate_blocks,
    _is_classifier_endpoint,
    _ledger_classifier_shift_targets,
    audit_payload,
    cmd_discovery_audit,
    collect_closurestatus_blocks,
    diagnose_closurestatus_block,
    diagnose_closurestatus_open_fields,
    discovery_integrity_payload,
    discovery_audit_payload,
    parser as bedc_parser,
)


class ClosurestatusRegexTests(unittest.TestCase):
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

    def test_positive_discovery_missing_gate_and_weight_errors(self) -> None:
        warnings, errors = diagnose_closurestatus_open_fields(
            self._block(
                open_fields={
                    "closureclaimkind": "positiveDiscovery",
                    "closurenamecert": "n",
                    "closureledger": "l",
                    "closureclassifierincrement": "1",
                }
            )
        )
        self.assertEqual(warnings, [])
        self.assertTrue(any("requires \\closuregate" in item["message"] for item in errors))
        self.assertTrue(
            any("requires \\closureweightprofile" in item["message"] for item in errors)
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


class DiscoveryAuditTests(unittest.TestCase):
    def _block(self, **overrides):
        base = {
            "file": "papers/bedc/parts/x.tex",
            "line": 10,
            "region": "Foo",
            "theory_closure": "scopedClosure",
            "formal_status": "theoremCheckedV",
            "lean_target": "BEDC.Foo.example",
            "bridge_status": "none",
            "origin": "ai",
            "raw_body": r"\scopeclosed{local packet}",
            "open_fields": {},
        }
        base.update(overrides)
        return base

    def test_discovery_audit_subcommand_dispatches_to_command(self) -> None:
        args = bedc_parser().parse_args(["discovery-audit", "--json"])
        self.assertIs(args.func, cmd_discovery_audit)
        self.assertTrue(args.json)

    def test_discovery_audit_reports_ledger_gaps(self) -> None:
        payload = discovery_audit_payload([
            self._block(open_fields={"closureclaimkind": "discovery"})
        ])
        kinds = {item["kind"] for item in payload["ledger_gaps"]}
        self.assertIn("missing_closurenamecert", kinds)
        self.assertIn("missing_closureledger", kinds)
        self.assertIn("missing_closureclassifierincrement", kinds)

    def test_discovery_audit_reports_positive_discovery_missing_positive_rows(self) -> None:
        payload = discovery_audit_payload([
            self._block(
                open_fields={
                    "closureclaimkind": "positiveDiscovery",
                    "closurenamecert": "NameCert row",
                    "closureledger": "positive gate ledger",
                    "closureclassifierincrement": "1",
                }
            )
        ])
        kinds = {item["kind"] for item in payload["ledger_gaps"]}
        self.assertIn("missing_closuregate", kinds)
        self.assertIn("missing_closureweightprofile", kinds)

    def test_discovery_audit_reports_scope_global_keyword_risk(self) -> None:
        payload = discovery_audit_payload([
            self._block(
                raw_body=r"\scopeclosed{This gives a global classifier.}",
                open_fields={"closureclaimkind": "discovery"},
            )
        ])
        self.assertEqual(payload["scope_global_risk_count"], 1)
        item = payload["scope_global_risks"][0]
        self.assertEqual(item["file"], "papers/bedc/parts/x.tex")
        self.assertEqual(item["line"], 10)
        self.assertEqual(item["evidence"], "global")

    def test_discovery_audit_reports_verification_ledger_gaps(self) -> None:
        payload = discovery_audit_payload([
            self._block(
                open_fields={
                    "closureclaimkind": "discovery",
                    "closurenamecert": "NameCert row",
                    "closureledger": "namecert rows",
                    "closureclassifierincrement": "1",
                }
            )
        ])
        kinds = {item["kind"] for item in payload["verification_ledger_gaps"]}
        self.assertIn("missing_transcription_ledger_cue", kinds)
        self.assertIn("missing_backend_ledger_cue", kinds)
        self.assertIn("missing_trust_ledger_cue", kinds)
        self.assertIn("missing_dependency_ledger_cue", kinds)

    def test_discovery_candidate_scope_excludes_non_candidate_blocks(self) -> None:
        cases = {
            "human_origin": self._block(origin="human"),
            "seed_closure": self._block(theory_closure="seedClosure"),
            "missing_theory_closure": self._block(theory_closure=None),
            "parser_error": self._block(error="unterminated closurestatus block"),
            "thematic_name_only": self._block(
                region="ClassifierNoveltyLedger",
                raw_body=r"\scopeclosed{This classifier novelty chapter is seed-level prose.}",
            ),
            "origin_ai_only": self._block(origin="ai"),
        }
        for name, block in cases.items():
            with self.subTest(name=name):
                self.assertEqual(_discovery_candidate_blocks([block]), [])
                payload = discovery_audit_payload([block])
                self.assertEqual(payload["candidate_count"], 0)
                self.assertEqual(payload["ledger_gap_count"], 0)
                self.assertEqual(payload["scope_global_risk_count"], 0)
                self.assertEqual(payload["verification_ledger_gap_count"], 0)
                self.assertEqual(payload["ledger_gaps"], [])
                self.assertEqual(payload["scope_global_risks"], [])
                self.assertEqual(payload["verification_ledger_gaps"], [])

    def test_discovery_audit_reports_unknown_ledger_kind(self) -> None:
        payload = discovery_audit_payload([
            self._block(
                open_fields={
                    "closureclaimkind": "discovery",
                    "closurenamecert": "NameCert row",
                    "closureledger": "opaque packet row",
                    "closureclassifierincrement": "1",
                }
            )
        ])
        matches = [
            item for item in payload["ledger_gaps"]
            if item["kind"] == "kind_unknown"
        ]
        self.assertEqual(len(matches), 1)
        self.assertEqual(matches[0]["evidence"], "opaque packet row")

    def test_discovery_audit_command_never_fails(self) -> None:
        args = type("Args", (), {"json": True, "verbose": False})()
        with patch("bedc_ci.collect_closurestatus_blocks", return_value=[self._block()]), \
            redirect_stdout(StringIO()):
            rc = cmd_discovery_audit(args)
        self.assertEqual(rc, 0)

    def test_discovery_integrity_parses_record_literal_classifier_shift(self) -> None:
        headers = {
            "BEDC.A.C": "def C (x y : BHist) : Prop :=",
            "BEDC.B.D": "def D (x y : BHist) : Prop :=",
            "BEDC.Target.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
        }
        bodies = {
            "BEDC.A.C": "def C (x y : BHist) : Prop := True",
            "BEDC.B.D": "def D (x y : BHist) : Prop := True",
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.A.C\n"
                "    AfterClassifier := BEDC.B.D\n"
                "  }"
            ),
        }
        before, after, shift_refs, notes = _ledger_classifier_shift_targets(
            "BEDC.Target.Ledger",
            headers,
            bodies,
            {"C": ["BEDC.A.C"], "D": ["BEDC.B.D"], "Ledger": ["BEDC.Target.Ledger"]},
        )
        self.assertEqual(before, ["BEDC.A.C"])
        self.assertEqual(after, ["BEDC.B.D"])
        self.assertEqual(shift_refs, ["BEDC.A.C", "BEDC.B.D"])
        self.assertEqual(notes, [])

    def test_binder_style_classifier_endpoint_is_recognized(self) -> None:
        self.assertTrue(_is_classifier_endpoint(
            "BEDC.A.C",
            {"BEDC.A.C": "def C (x y : BHist) : Prop :="},
        ))
        self.assertTrue(_is_classifier_endpoint(
            "BEDC.A.C",
            {"BEDC.A.C": "def C (x : BHist) (y : BHist) : Prop :="},
        ))

    def test_discovery_integrity_ignores_thematic_existing_surface_without_claim(self) -> None:
        payload = discovery_integrity_payload(
            [self._block(region="ClassifierNoveltyLedger")],
            LeanSourceScan([], [], {}, {}, []),
        )
        self.assertEqual(payload["declared_discovery_chapter_count"], 0)
        self.assertEqual(payload["checked_chapter_count"], 0)
        self.assertEqual(payload["unresolved_count"], 0)
        self.assertEqual(payload["violation_count"], 0)

    def test_discovery_integrity_blocks_declared_positive_without_shift(self) -> None:
        headers = {
            "BEDC.Fake.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
        }
        bodies = {
            "BEDC.Fake.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := none"
            ),
        }
        ledger = DiscoveryDeltaLedgerRecord(
            "Ledger",
            "BEDC.Fake.Ledger",
            "lean4/BEDC/Fake.lean",
            1,
            "Fake",
            "fake",
            False,
        )
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closureledger": "BEDC.Fake.Ledger",
            },
        )
        payload = discovery_integrity_payload(
            [block],
            LeanSourceScan([], [], headers, bodies, [ledger]),
        )
        self.assertEqual(payload["declared_discovery_chapter_count"], 1)
        self.assertEqual(payload["checked_chapter_count"], 0)
        self.assertEqual(payload["unresolved_count"], 1)
        self.assertEqual(payload["violation_count"], 1)
        self.assertEqual(
            payload["violations"][0]["kind"],
            "declared_discovery_classifier_unresolved",
        )

    def test_discovery_integrity_accepts_marker_linked_shifted_ledger_surface(self) -> None:
        headers = {
            "BEDC.A.C": "def C (x y : BHist) : Prop :=",
            "BEDC.B.D": "def D (x y : BHist) : Prop :=",
            "BEDC.Target.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
        }
        bodies = {
            "BEDC.A.C": "def C (x y : BHist) : Prop := True",
            "BEDC.B.D": "def D (x y : BHist) : Prop := False",
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.A.C\n"
                "    AfterClassifier := BEDC.B.D\n"
                "  }"
            ),
        }
        ledger = DiscoveryDeltaLedgerRecord(
            "Ledger",
            "BEDC.Target.Ledger",
            "lean4/BEDC/Target.lean",
            1,
            "Target",
            "target",
            True,
        )
        block = self._block(raw_body=r"\leanchecked{BEDC.Target.Ledger}")
        fps = {
            "BEDC.A.C": ExprFingerprint(
                "a", "type", "a", reduced_fingerprint="old"
            ),
            "BEDC.B.D": ExprFingerprint(
                "b", "type", "b", reduced_fingerprint="fresh"
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload(
                [block],
                LeanSourceScan([], [], headers, bodies, [ledger]),
            )
        self.assertEqual(payload["declared_discovery_chapter_count"], 1)
        self.assertEqual(payload["explicit_discovery_chapter_count"], 0)
        self.assertEqual(payload["checked_chapter_count"], 1)
        self.assertEqual(payload["violation_count"], 0)

    def test_discovery_integrity_blocks_binder_style_reconstruction(self) -> None:
        headers = {
            "BEDC.Prior.OldRel": "def OldRel (x y : BHist) : Prop :=",
            "BEDC.Target.NewRel": "def NewRel (x y : BHist) : Prop :=",
        }
        bodies = {
            "BEDC.Prior.OldRel": "def OldRel (x y : BHist) : Prop := True",
            "BEDC.Target.NewRel": "def NewRel (x y : BHist) : Prop := True",
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.Prior.OldRel\n"
                "    AfterClassifier := BEDC.Target.NewRel\n"
                "  }"
            ),
        }
        headers["BEDC.Target.Ledger"] = "def Ledger : DiscoveryDeltaLedger X :="
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closureledger": "BEDC.Target.Ledger",
            },
        )
        ledger = DiscoveryDeltaLedgerRecord(
            "Ledger",
            "BEDC.Target.Ledger",
            "lean4/BEDC/Target.lean",
            1,
            "Target",
            "target",
            True,
        )
        scan = LeanSourceScan([], [], headers, bodies, [ledger])
        fps = {
            "BEDC.Prior.OldRel": ExprFingerprint(
                "old", "type", "old", reduced_fingerprint="same"
            ),
            "BEDC.Target.NewRel": ExprFingerprint(
                "new", "type", "new", reduced_fingerprint="same"
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload([block], scan)
        self.assertEqual(payload["checked_chapter_count"], 1)
        self.assertEqual(payload["violation_count"], 1)
        self.assertEqual(
            payload["violations"][0]["kind"],
            "structural_reconstruction_discovery_claim",
        )

    def test_discovery_integrity_keeps_qualified_same_local_names_distinct(self) -> None:
        headers = {
            "BEDC.A.C": "def C (x y : BHist) : Prop :=",
            "BEDC.B.C": "def C (x y : BHist) : Prop :=",
        }
        bodies = {
            "BEDC.A.C": "def C (x y : BHist) : Prop := True",
            "BEDC.B.C": "def C (x y : BHist) : Prop := False",
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.A.C\n"
                "    AfterClassifier := BEDC.B.C\n"
                "  }"
            ),
        }
        headers["BEDC.Target.Ledger"] = "def Ledger : DiscoveryDeltaLedger X :="
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closureledger": "BEDC.Target.Ledger",
            },
        )
        ledger = DiscoveryDeltaLedgerRecord(
            "Ledger",
            "BEDC.Target.Ledger",
            "lean4/BEDC/Target.lean",
            1,
            "Target",
            "target",
            True,
        )
        scan = LeanSourceScan([], [], headers, bodies, [ledger])
        fps = {
            "BEDC.A.C": ExprFingerprint(
                "a", "type", "a", reduced_fingerprint="ra"
            ),
            "BEDC.B.C": ExprFingerprint(
                "b", "type", "b", reduced_fingerprint="rb"
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload([block], scan)
        self.assertEqual(payload["checked_chapter_count"], 1)
        self.assertEqual(payload["violation_count"], 0)
        provenance = payload["sites"][0]["provenance"]
        self.assertTrue(all(item["prior"] != "BEDC.B.C" for item in provenance))


if __name__ == "__main__":
    unittest.main(verbosity=2)

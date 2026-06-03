"""Unit tests for the closurestatus block parser in bedc_ci.py."""
from __future__ import annotations

import sys
import unittest
import json
import threading
import time
from contextlib import nullcontext, redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
sys.path.insert(0, str(Path(__file__).parents[2] / "tools"))
from bedc_ci import (  # type: ignore[import-not-found]
    CLOSURESTATUS_BEGIN_RE,
    CLOSURESTATUS_FIELD_RE,
    DeclarationRecord,
    DiscoveryDeltaLedgerRecord,
    ExprFingerprint,
    KernelAssertionCheck,
    LeanSourceScan,
    _discovery_candidate_blocks,
    _is_classifier_endpoint,
    _structural_dna_relation_unavailable,
    _ledger_classifier_shift_targets,
    audit_payload,
    cmd_audit,
    cmd_discovery_audit,
    collect_closurestatus_blocks,
    diagnose_closurestatus_block,
    diagnose_closurestatus_open_fields,
    discovery_integrity_payload,
    discovery_assert_gate_payload,
    discovery_gate_witness_kernel_grounding,
    load_discovery_gate_witnesses,
    discovery_audit_payload,
    discovery_nonasserted_hygiene_payload,
    discovery_production_radar_payload,
    cmd_discovery_radar,
    parser as bedc_parser,
)
from discovery_refutation_publisher import (  # type: ignore[import-not-found]
    ledger_content_signature,
    merge_records,
    refutation_records_from_payload,
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
                "a", "type", "a", reduced_fingerprint="old",
                canonical_reduced_payload="payload-old",
            ),
            "BEDC.B.D": ExprFingerprint(
                "b", "type", "b", reduced_fingerprint="fresh",
                canonical_reduced_payload="payload-fresh",
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
                "old", "type", "old", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
            "BEDC.Target.NewRel": ExprFingerprint(
                "new", "type", "new", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
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
        self.assertEqual(payload["violations"][0]["canonical_payload"], "payload-same")

    def test_discovery_integrity_does_not_reconstruct_on_fingerprint_only_collision(self) -> None:
        headers = {
            "BEDC.Prior.OldRel": "inductive OldRel : BHist → Prop",
            "BEDC.Target.NewRel": "inductive NewRel : BHist → Prop",
            "BEDC.Target.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
        }
        bodies = {
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.Prior.OldRel\n"
                "    AfterClassifier := BEDC.Target.NewRel\n"
                "  }"
            ),
        }
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
                "coarse", "type", "", reduced_fingerprint="same64",
                canonical_reduced_payload="(inductive|OldRel|ctors=1)",
            ),
            "BEDC.Target.NewRel": ExprFingerprint(
                "coarse", "type", "", reduced_fingerprint="same64",
                canonical_reduced_payload="(inductive|NewRel|ctors=2)",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload([block], scan)
        self.assertEqual(payload["checked_chapter_count"], 1)
        self.assertEqual(payload["violation_count"], 0)
        reconstruction = [
            item for item in payload["sites"][0]["provenance"]
            if item.get("relation") == "reconstruction"
        ]
        self.assertEqual(reconstruction, [])

    def test_discovery_integrity_empty_payload_does_not_emit_reconstruction(self) -> None:
        headers = {
            "BEDC.Prior.OldRel": "def OldRel (x y : BHist) : Prop :=",
            "BEDC.Target.NewRel": "def NewRel (x y : BHist) : Prop :=",
            "BEDC.Target.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
        }
        bodies = {
            "BEDC.Target.Ledger": (
                "def Ledger : DiscoveryDeltaLedger X where\n"
                "  classifier_shift := some {\n"
                "    BeforeClassifier := BEDC.Prior.OldRel\n"
                "    AfterClassifier := BEDC.Target.NewRel\n"
                "  }"
            ),
        }
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
                "old", "type", "old", reduced_fingerprint="same",
            ),
            "BEDC.Target.NewRel": ExprFingerprint(
                "new", "type", "new", reduced_fingerprint="same",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload([block], scan)
        self.assertEqual(payload["checked_chapter_count"], 0)
        self.assertEqual(payload["violation_count"], 0)
        self.assertTrue(any(
            item.get("reason") == "structural_dna_canonical_payload_unavailable"
            for item in payload["unavailable"]
        ))

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
                "a", "type", "a", reduced_fingerprint="ra",
                canonical_reduced_payload="payload-a",
            ),
            "BEDC.B.C": ExprFingerprint(
                "b", "type", "b", reduced_fingerprint="rb",
                canonical_reduced_payload="payload-b",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            payload = discovery_integrity_payload([block], scan)
        self.assertEqual(payload["checked_chapter_count"], 1)
        self.assertEqual(payload["violation_count"], 0)
        provenance = payload["sites"][0]["provenance"]
        self.assertTrue(all(item["prior"] != "BEDC.B.C" for item in provenance))

    def test_relation_unavailable_does_not_pollute_provenance(self) -> None:
        headers = {
            "BEDC.A.C": "def C (x y : BHist) : Prop :=",
            "BEDC.B.C": "def C (x y : BHist) : Prop :=",
            "BEDC.Target.Ledger": "def Ledger : DiscoveryDeltaLedger X :=",
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
        ledger = DiscoveryDeltaLedgerRecord(
            "Ledger",
            "BEDC.Target.Ledger",
            "lean4/BEDC/Target.lean",
            1,
            "Target",
            "target",
            True,
        )
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closureledger": "BEDC.Target.Ledger",
            },
        )
        scan = LeanSourceScan([], [], headers, bodies, [ledger])
        fps = {
            "BEDC.A.C": ExprFingerprint(
                "a", "type", "a", reduced_fingerprint="ra",
                canonical_reduced_payload="payload-a",
            ),
            "BEDC.B.C": ExprFingerprint(
                "b", "type", "b", reduced_fingerprint="rb",
                canonical_reduced_payload="payload-b",
            ),
        }
        unavailable = _structural_dna_relation_unavailable("forced_unavailable")
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps), \
            patch("bedc_ci._run_structural_dna_relations", return_value=([], unavailable)):
            payload = discovery_integrity_payload([block], scan)
        site = payload["sites"][0]
        self.assertTrue(all("prior" in item for item in site["provenance"]))
        self.assertTrue(all(
            item.get("relation") != "relation_analysis_unavailable"
            for item in site["provenance"]
        ))
        self.assertEqual(len(site["unavailable"]), 1)
        self.assertEqual(site["unavailable"][0]["relation"], "relation_analysis_unavailable")
        self.assertEqual(len(payload["relation_diagnostics"]), 1)
        self.assertEqual(
            payload["relation_diagnostics"][0]["relation"],
            "relation_analysis_unavailable",
        )
        self.assertEqual(len(site["relation_diagnostics"]), 1)
        self.assertEqual(
            site["relation_diagnostics"][0]["relation"],
            "relation_analysis_unavailable",
        )
        self.assertEqual(payload["relation_diagnostics_count"], 1)

    def test_positive_discovery_deferred_structural_check_fails_g2(self) -> None:
        target = "BEDC.Target.Gate"
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closuregate": target,
                "closureledger": "ledger",
                "closureclassifierincrement": "1",
                "closurenamecert": "namecert",
                "closureweightprofile": "weight",
            },
            scopeclosed="local scope",
            has_scope=True,
        )
        headers = {target: "def Gate : PositiveDiscovery Foo :="}
        bodies = {target: "def Gate : PositiveDiscovery Foo := witness"}
        decls = [DeclarationRecord("BEDC.Target", "lean4/BEDC/Target.lean", 1, "def", "Gate", target)]
        scan = LeanSourceScan(decls, [], headers, bodies, [])
        kernel = KernelAssertionCheck(
            target=target,
            module="BEDC.Target",
            module_reachable=True,
            olean_exists=True,
            check_ok=True,
            axioms_parsed=True,
            axioms=(),
            forbidden_axioms=(),
            returncode=0,
        )
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}):
            payload = discovery_assert_gate_payload(
                [block],
                scan,
                {
                    "sites": [{
                        "file": block["file"],
                        "line": block["line"],
                        "region": "FooUp",
                        "resolution_status": "unresolved",
                    }],
                    "violations": [],
                },
                sieve_payload={"targets": []},
            )
        site = payload["asserted_sites"][0]
        g2 = [gate for gate in site["gates"] if gate["gate"] == "G2"][0]
        self.assertEqual(g2["status"], "FAIL")
        self.assertIn("unavailable or unresolved", g2["reason"])

    def test_positive_discovery_unreachable_target_fails_g0(self) -> None:
        target = "BEDC.Target.Gate"
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closuregate": target,
                "closureledger": "ledger",
                "closureclassifierincrement": "1",
                "closurenamecert": "namecert",
                "closureweightprofile": "weight",
            },
            scopeclosed="local scope",
            has_scope=True,
        )
        headers = {target: "def Gate : PositiveDiscovery Foo :="}
        bodies = {target: "def Gate : PositiveDiscovery Foo := witness"}
        decls = [DeclarationRecord("BEDC.Target", "lean4/BEDC/Target.lean", 1, "def", "Gate", target)]
        scan = LeanSourceScan(decls, [], headers, bodies, [])
        kernel = KernelAssertionCheck(
            target=target,
            module="BEDC.Target",
            module_reachable=False,
            olean_exists=False,
            check_ok=False,
            axioms_parsed=False,
            axioms=(),
            forbidden_axioms=(),
            returncode=1,
            message="target module is not reachable from import BEDC",
        )
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}):
            payload = discovery_assert_gate_payload(
                [block],
                scan,
                {"sites": [], "violations": []},
                sieve_payload={"targets": []},
            )
        g0 = [gate for gate in payload["asserted_sites"][0]["gates"] if gate["gate"] == "G0"][0]
        self.assertEqual(g0["status"], "FAIL")
        self.assertIn("kernel-checkable", g0["reason"])

    def test_conjectured_refuted_missing_evidence_hygiene_fails(self) -> None:
        payload = discovery_nonasserted_hygiene_payload([
            self._block(open_fields={"closureclaimkind": "conjecturedDiscovery"}, lean_target=None),
            self._block(open_fields={"closureclaimkind": "refutedDiscovery"}, lean_target=None),
        ])
        self.assertEqual(payload["site_count"], 2)
        self.assertEqual(payload["failure_count"], 2)
        self.assertTrue(all(item["gate_status"] == "FAIL" for item in payload["failures"]))

    def test_assert_gate_is_lazy_without_positive_discovery(self) -> None:
        block = self._block(open_fields={"closureclaimkind": "conjecturedDiscovery"})
        scan = LeanSourceScan([], [], {}, {}, [])
        with patch("bedc_ci._kernel_assertion_checks") as kernel_checks:
            payload = discovery_assert_gate_payload(
                [block],
                scan,
                {"sites": [], "violations": []},
                sieve_payload={"targets": []},
            )
        kernel_checks.assert_not_called()
        self.assertEqual(payload["asserted_count"], 0)
        self.assertEqual(payload["failure_count"], 0)
        self.assertEqual(payload["conjectured_count"], 1)

    def _assert_gate_fixture(self, target: str = "BEDC.Target.Gate") -> tuple[dict, LeanSourceScan, KernelAssertionCheck]:
        prior = "BEDC.Prior.Old"
        block = self._block(
            open_fields={
                "closureclaimkind": "positiveDiscovery",
                "closuregate": target,
                "closureparents": prior,
                "closureledger": "ledger",
                "closureclassifierincrement": "1",
                "closurenamecert": "namecert",
                "closureweightprofile": "weight",
            },
            scopeclosed="local scope",
            has_scope=True,
        )
        headers = {target: "def Gate : PositiveDiscovery Foo :="}
        bodies = {target: "def Gate : PositiveDiscovery Foo := witness"}
        decls = [DeclarationRecord("BEDC.Target", "lean4/BEDC/Target.lean", 1, "def", "Gate", target)]
        scan = LeanSourceScan(decls, [], headers, bodies, [])
        kernel = KernelAssertionCheck(
            target=target,
            module="BEDC.Target",
            module_reachable=True,
            olean_exists=True,
            check_ok=True,
            axioms_parsed=True,
            axioms=(),
            forbidden_axioms=(),
            returncode=0,
        )
        return block, scan, kernel

    def _exact_witness(
        self,
        target: str = "BEDC.Target.Gate",
        canonical_payload: str = "payload-same",
        reduced_fp: str = "same",
    ) -> dict:
        return {
            "id": "test-target-reconstruction",
            "kind": "reconstruction",
            "pattern": {
                "target": target,
                "prior": "BEDC.Prior.Old",
                "canonical_payload": canonical_payload,
                "reduced_fp": reduced_fp,
            },
            "refutes_because": "test target is an exact kernel-grounded reconstruction pseudo",
            "kernel_grounded": True,
            "soundness": "canonical_payload_equal",
            "provenance": {"source": "unit"},
            "regression_candidate": target,
            "added": "2026-06-02T00:00:00",
        }

    def _exact_integrity(
        self,
        target: str = "BEDC.Target.Gate",
        canonical_payload: str = "payload-same",
        reduced_fp: str = "same",
    ) -> dict:
        return {
            "sites": [{
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "resolution_status": "resolved",
                "before_classifiers": ["BEDC.Prior.Old"],
                "declared_new_classifiers": [target],
                "provenance": [{
                    "candidate": target,
                    "prior": "BEDC.Prior.Old",
                    "relation": "reconstruction",
                    "candidate_reduced_fp": reduced_fp,
                    "reduced_fp": reduced_fp,
                    "canonical_payload": canonical_payload,
                    "candidate_canonical_payload": canonical_payload,
                    "prior_canonical_payload": canonical_payload,
                    "evidence": "canonical_payload_equal",
                }],
            }],
            "violations": [],
        }

    def test_discovery_gate_empty_witness_registry_does_not_add_gate(self) -> None:
        target = "BEDC.Target.Gate"
        block, scan, kernel = self._assert_gate_fixture(target)
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}), \
                patch("bedc_ci.load_discovery_gate_witnesses", return_value=([], [])):
            payload = discovery_assert_gate_payload(
                [block],
                scan,
                {"sites": [], "violations": []},
                sieve_payload={"targets": []},
            )
        site = payload["asserted_sites"][0]
        self.assertNotIn("W", [gate["gate"] for gate in site["gates"]])
        self.assertEqual(payload["witness_count"], 0)
        self.assertEqual(payload["witness_registry_diagnostic_count"], 0)

    def test_discovery_gate_witness_registry_blocks_matching_pseudo(self) -> None:
        target = "BEDC.Target.Gate"
        block, scan, kernel = self._assert_gate_fixture(target)
        witness = self._exact_witness(target)
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}), \
                patch("bedc_ci.load_discovery_gate_witnesses", return_value=([witness], [])):
            payload = discovery_assert_gate_payload(
                [block],
                scan,
                self._exact_integrity(target),
                sieve_payload={"targets": []},
            )
        site = payload["asserted_sites"][0]
        w_gate = [gate for gate in site["gates"] if gate["gate"] == "W"][0]
        self.assertEqual(w_gate["status"], "FAIL")
        self.assertEqual(site["status"], "FAIL")
        self.assertIn("W", site["failed_gates"])
        self.assertEqual(w_gate["details"]["witnesses"][0]["id"], witness["id"])

    def test_discovery_gate_witness_registry_is_monotonic_negative(self) -> None:
        target = "BEDC.Target.Gate"
        block, scan, kernel = self._assert_gate_fixture(target)
        witness = self._exact_witness(target)
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}), \
                patch("bedc_ci.load_discovery_gate_witnesses", return_value=([], [])):
            before = discovery_assert_gate_payload(
                [block],
                scan,
                self._exact_integrity(target),
                sieve_payload={"targets": []},
            )
        with patch("bedc_ci._kernel_assertion_checks", return_value={target: kernel}), \
                patch("bedc_ci.load_discovery_gate_witnesses", return_value=([witness], [])):
            after = discovery_assert_gate_payload(
                [block],
                scan,
                self._exact_integrity(target),
                sieve_payload={"targets": []},
            )
        before_keys = {
            (item["file"], item["line"], item["target"], item["gate"])
            for item in before["failures"]
        }
        after_keys = {
            (item["file"], item["line"], item["target"], item["gate"])
            for item in after["failures"]
        }
        self.assertTrue(before_keys.issubset(after_keys))
        self.assertIn(("papers/bedc/parts/x.tex", 10, target, "W"), after_keys)

    def test_discovery_gate_witness_registry_loader_rejects_poisoned_grounding(self) -> None:
        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "witnesses.json"
            path.write_text(json.dumps([{
                "id": "bad",
                "kind": "reconstruction",
                "pattern": {
                    "target": "BEDC.Target.Gate",
                    "prior": "BEDC.Prior.Old",
                    "reduced_fp": "claimed-same",
                },
                "kernel_grounded": True,
            }]), encoding="utf-8")
            fps = {
                "BEDC.Target.Gate": ExprFingerprint("target", "type", "value", reduced_fingerprint="actual-target"),
                "BEDC.Prior.Old": ExprFingerprint("prior", "type", "value", reduced_fingerprint="actual-prior"),
            }
            with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
                witnesses, diagnostics = load_discovery_gate_witnesses(path)
        self.assertEqual(witnesses, [])
        self.assertEqual(diagnostics[0]["kind"], "invalid_discovery_gate_witness_pattern")

    def test_discovery_gate_witness_kernel_grounding_recomputes_exact_match(self) -> None:
        witness = self._exact_witness("BEDC.Target.Gate", "payload-same", "same")
        fps = {
            "BEDC.Target.Gate": ExprFingerprint(
                "target", "type", "value", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
            "BEDC.Prior.Old": ExprFingerprint(
                "prior", "type", "value", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
            grounded, details = discovery_gate_witness_kernel_grounding(witness)
        self.assertTrue(grounded)
        self.assertEqual(details["target_reduced_fp"], "same")
        self.assertEqual(details["evidence"], "canonical_payload_equal")

    def test_discovery_gate_witness_registry_loader_rejects_wide_pattern(self) -> None:
        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "witnesses.json"
            path.write_text(json.dumps([{
                "id": "wide",
                "kind": "reconstruction",
                "pattern": {"kind": "reconstruction", "reason_tag": "duplicate_classifier"},
                "kernel_grounded": True,
            }]), encoding="utf-8")
            witnesses, diagnostics = load_discovery_gate_witnesses(path)
        self.assertEqual(witnesses, [])
        self.assertEqual(diagnostics[0]["kind"], "invalid_discovery_gate_witness_pattern")

    def test_discovery_gate_witness_registry_schema_envelope_allows_empty_registry(self) -> None:
        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "witnesses.json"
            path.write_text(json.dumps({
                "schema": "bedc.discovery_gate_witness_registry",
                "witness_schema": {"pattern": {"target": "", "prior": "", "canonical_payload": ""}},
                "witnesses": [],
            }), encoding="utf-8")
            witnesses, diagnostics = load_discovery_gate_witnesses(path)
        self.assertEqual(witnesses, [])
        self.assertEqual(diagnostics, [])

    def test_discovery_gate_witness_registry_loader_rejects_duplicate_and_conflict(self) -> None:
        with TemporaryDirectory() as tmp:
            duplicate_path = Path(tmp) / "duplicates.json"
            duplicate_path.write_text(json.dumps([
                self._exact_witness("BEDC.Target.Gate", "payload-same", "same"),
                {**self._exact_witness("BEDC.Target.Gate", "payload-same", "same"), "id": "dup"},
            ]), encoding="utf-8")
            fps = {
                "BEDC.Target.Gate": ExprFingerprint(
                    "target", "type", "value", reduced_fingerprint="same",
                    canonical_reduced_payload="payload-same",
                ),
                "BEDC.Prior.Old": ExprFingerprint(
                    "prior", "type", "value", reduced_fingerprint="same",
                    canonical_reduced_payload="payload-same",
                ),
            }
            with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
                witnesses, diagnostics = load_discovery_gate_witnesses(duplicate_path)
            self.assertEqual(len(witnesses), 1)
            self.assertEqual(diagnostics[0]["kind"], "duplicate_discovery_gate_witness")

            conflict_path = Path(tmp) / "conflicts.json"
            conflict_path.write_text(json.dumps([
                self._exact_witness("BEDC.Target.Gate", "payload-same", "same"),
                {**self._exact_witness("BEDC.Target.Gate", "payload-other", "same"), "id": "conflict"},
            ]), encoding="utf-8")
            with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps):
                witnesses, diagnostics = load_discovery_gate_witnesses(conflict_path)
            self.assertEqual(len(witnesses), 1)
            self.assertEqual(diagnostics[0]["kind"], "conflicting_discovery_gate_witness")

    def test_discovery_gate_evolver_rejects_poisoned_record_before_append(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        record = {
            "id": "poison",
            "kind": "reconstruction",
            "target": "BEDC.Target.Gate",
            "prior": "BEDC.Prior.Old",
            "reduced_fp": "claimed-same",
            "kernel_grounded": True,
        }
        fps = {
            "BEDC.Target.Gate": ExprFingerprint(
                "target", "type", "value", reduced_fingerprint="actual-target",
                canonical_reduced_payload="target-payload",
            ),
            "BEDC.Prior.Old": ExprFingerprint(
                "prior", "type", "value", reduced_fingerprint="actual-prior",
                canonical_reduced_payload="prior-payload",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps), \
                patch.object(discovery_gate_evolver, "_BEDC_CI", sys.modules["bedc_ci"]):
            witness, reason = discovery_gate_evolver.witness_from_record(record)
        self.assertIsNone(witness)
        self.assertIn("canonical_payload", str(reason))

    def test_discovery_gate_evolver_append_rechecks_kernel_grounding(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        witness = self._exact_witness("BEDC.Target.Gate", "payload-same", "same")
        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "witnesses.json"
            path.write_text("[]\n", encoding="utf-8")
            fps = {
                "BEDC.Target.Gate": ExprFingerprint(
                    "target", "type", "value", reduced_fingerprint="same",
                    canonical_reduced_payload="payload-same",
                ),
                "BEDC.Prior.Old": ExprFingerprint(
                    "prior", "type", "value", reduced_fingerprint="same",
                    canonical_reduced_payload="payload-same",
                ),
            }
            with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps), \
                    patch.object(discovery_gate_evolver, "_BEDC_CI", sys.modules["bedc_ci"]):
                self.assertTrue(discovery_gate_evolver.append_witness(path, witness))
            loaded = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(loaded[0]["soundness"], "canonical_payload_equal")
        self.assertEqual(loaded[0]["kernel_grounding"]["target_reduced_fp"], "same")

    def test_discovery_gate_evolver_vacuous_monotonic_only_escalates(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        witness = self._exact_witness("BEDC.Target.Gate", "payload-same", "same")
        payload = {"discovery_assert_gate": {"asserted_count": 0, "failures": []}}
        calls: list[str] = []
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean4" / "scripts").mkdir(parents=True)
            (root / "papers" / "bedc").mkdir(parents=True)
            with patch.object(discovery_gate_evolver, "run_cmd") as run_cmd, \
                    patch.object(discovery_gate_evolver, "audit_failures", return_value=(0, set(), payload)), \
                    patch.object(discovery_gate_evolver, "append_log", side_effect=calls.append), \
                    patch.object(discovery_gate_evolver, "ensure_allowed_changes"):
                run_cmd.return_value.returncode = 0
                run_cmd.return_value.stdout = ""
                run_cmd.return_value.stderr = ""
                discovery_gate_evolver.verify(
                    root,
                    witness,
                    no_push=True,
                    before_rc=0,
                    before_failures=set(),
                )
        self.assertTrue(any("asserted_count=0" in item and "not a soundness proof" in item for item in calls))

    def test_discovery_gate_evolver_worktree_prep_failure_escalates_without_crash(self) -> None:
        import argparse
        import discovery_gate_evolver  # type: ignore[import-not-found]

        record = {
            "id": "exact",
            "kind": "reconstruction",
            "target": "BEDC.Target.Gate",
            "prior": "BEDC.Prior.Old",
            "canonical_payload": "payload-same",
            "reduced_fp": "same",
        }
        fps = {
            "BEDC.Target.Gate": ExprFingerprint(
                "target", "type", "value", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
            "BEDC.Prior.Old": ExprFingerprint(
                "prior", "type", "value", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
        }
        calls: list[str] = []
        args = argparse.Namespace(worktree="/tmp/bedc-test-prep-failure", base_ref="HEAD", no_push=False)
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fps), \
                patch.object(discovery_gate_evolver, "_BEDC_CI", sys.modules["bedc_ci"]), \
                patch.object(discovery_gate_evolver, "prepare_worktree", side_effect=RuntimeError("fetch failed")), \
                patch.object(discovery_gate_evolver, "cleanup_worktree") as cleanup, \
                patch.object(discovery_gate_evolver, "append_log", side_effect=calls.append):
            ok = discovery_gate_evolver.process_one(record, args)
        self.assertFalse(ok)
        cleanup.assert_not_called()
        self.assertTrue(any("worktree prep failed" in item for item in calls))

    def test_discovery_adversarial_generator_once_load_error_is_nonzero(self) -> None:
        import discovery_adversarial_generator  # type: ignore[import-not-found]

        with patch.object(discovery_adversarial_generator, "pid_lock", return_value=nullcontext()), \
                patch.object(
                    discovery_adversarial_generator,
                    "bedc_ci_module",
                    side_effect=RuntimeError("bedc_ci unavailable"),
                ), \
                patch.object(discovery_adversarial_generator, "append_log"), \
                patch.object(sys, "argv", ["discovery_adversarial_generator.py", "--once"]), \
                redirect_stdout(StringIO()) as stdout:
            rc = discovery_adversarial_generator.main()
        self.assertNotEqual(rc, 0)
        payload = json.loads(stdout.getvalue())
        self.assertEqual(payload["status"], "error")
        self.assertEqual(payload["error_type"], "RuntimeError")

    def test_discovery_adversarial_generator_skips_output_covered_bucket(self) -> None:
        import argparse
        import discovery_adversarial_generator  # type: ignore[import-not-found]

        class FakeCi:
            def scan_lean_sources(self):
                return object()

        existing = {
            "schema": "bedc.discovery_adversarial_generator.proven_pseudo",
            "target": "BEDC.Target.First",
            "prior": "BEDC.Prior.Old",
            "canonical_payload": "payload-same",
        }
        with TemporaryDirectory() as tmp:
            output = Path(tmp) / "proven_pseudos.jsonl"
            output.write_text(json.dumps(existing) + "\n", encoding="utf-8")
            args = argparse.Namespace(
                output=str(output),
                classifier_cap=20,
                max_new_per_bucket=1,
                max_records=10,
            )
            with patch.object(discovery_adversarial_generator, "ensure_structural_dna_build", return_value=None), \
                    patch.object(discovery_adversarial_generator, "bedc_ci_module", return_value=FakeCi()), \
                    patch.object(discovery_adversarial_generator, "load_registry_keys", return_value=(set(), 0, 100)), \
                    patch.object(
                        discovery_adversarial_generator,
                        "positive_discovery_assertion_target",
                        return_value=("BEDC.Assert.Gate", ["BEDC.Support.Target"]),
                    ), \
                    patch.object(
                        discovery_adversarial_generator,
                        "classifier_payload_buckets",
                        return_value=[{
                            "canonical_payload": "payload-same",
                            "names": ["BEDC.Prior.Old", "BEDC.Target.Second"],
                            "reduced_fps": {
                                "BEDC.Prior.Old": "same",
                                "BEDC.Target.Second": "same",
                            },
                        }],
                    ), \
                    patch.object(discovery_adversarial_generator, "grounded_canonical_refutation") as grounding, \
                    patch.object(discovery_adversarial_generator, "true_gate_passed") as gate_passed, \
                    patch.object(discovery_adversarial_generator, "append_log"):
                result = discovery_adversarial_generator.run_once(args)
            lines = output.read_text(encoding="utf-8").splitlines()
        self.assertEqual(result["status"], "no-hit")
        self.assertEqual(result["emitted"], 0)
        self.assertEqual(result["skipped_covered"], 1)
        self.assertEqual(len(lines), 1)
        grounding.assert_not_called()
        gate_passed.assert_not_called()

    def test_discovery_gate_evolver_verify_failure_does_not_count_ok(self) -> None:
        import argparse
        import discovery_gate_evolver  # type: ignore[import-not-found]

        witness = {
            "id": "exact",
            "kind": "reconstruction",
            "pattern": {
                "target": "BEDC.Target.Gate",
                "prior": "BEDC.Prior.Old",
                "canonical_payload": "payload-same",
            },
            "soundness": "canonical_payload_equal",
        }
        args = argparse.Namespace(worktree="/tmp/bedc-test-verify-failure", base_ref="HEAD", no_push=True)
        with patch.object(discovery_gate_evolver, "witness_from_record", return_value=(witness, None)), \
                patch.object(discovery_gate_evolver, "prepare_worktree"), \
                patch.object(discovery_gate_evolver, "audit_failures", return_value=(0, set(), {})), \
                patch.object(discovery_gate_evolver, "registry_bucket_keys", return_value=set()), \
                patch.object(discovery_gate_evolver, "append_witness", return_value=True), \
                patch.object(discovery_gate_evolver, "append_regression_test"), \
                patch.object(discovery_gate_evolver, "verify", side_effect=RuntimeError("verify failed")), \
                patch.object(discovery_gate_evolver, "commit_and_push") as commit_and_push, \
                patch.object(discovery_gate_evolver, "append_log"):
            ok_count, fail_count = discovery_gate_evolver.process_records([{"id": "exact"}], args)
        self.assertEqual(ok_count, 0)
        self.assertEqual(fail_count, 1)
        commit_and_push.assert_not_called()

    # BEGIN DISCOVERY GATE EVOLVER REGRESSION TESTS
    # END DISCOVERY GATE EVOLVER REGRESSION TESTS

    def _radar_payload(
        self,
        integrity: dict[str, object],
        sieve: dict[str, object] | None = None,
        assert_gate: dict[str, object] | None = None,
        scan: LeanSourceScan | None = None,
        full_corpus_scan: bool = False,
    ) -> dict[str, object]:
        return discovery_production_radar_payload(
            [self._block()],
            scan or LeanSourceScan([], [], {}, {}, []),
            discovery_integrity=integrity,
            sieve_payload=sieve or {"targets": []},
            discovery_assert_gate=assert_gate or {"asserted_sites": []},
            full_corpus_scan=full_corpus_scan,
        )

    def test_discovery_radar_refutes_prior_reconstruction(self) -> None:
        integrity = {
            "sites": [{
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "chapter_key": "foo",
                "claim_kind": "positiveDiscovery",
                "sources": ["DiscoveryDeltaLedger.classifier_shift"],
                "ledger": "BEDC.Target.Ledger",
                "before_classifiers": ["BEDC.Prior.Old"],
                "declared_new_classifiers": ["BEDC.Target.New"],
                "resolution_status": "resolved",
                "provenance": [{
                    "candidate": "BEDC.Target.New",
                    "prior": "BEDC.Prior.Old",
                    "relation": "reconstruction",
                    "candidate_reduced_fp": "same",
                    "reduced_fp": "same",
                }],
            }],
            "violations": [{
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "kind": "structural_reconstruction_discovery_claim",
                "candidate": "BEDC.Target.New",
                "prior_classifier": "BEDC.Prior.Old",
            }],
        }
        payload = self._radar_payload(integrity)
        self.assertEqual(payload["refuted_count"], 1)
        candidate = payload["candidates"][0]
        self.assertEqual(candidate["state"], "refuted")
        self.assertEqual(
            candidate["phase_a"]["binary_novelty_signal"],
            "reconstruction",
        )
        self.assertIn("phase_a_structural_reconstruction", candidate["evidence"])

    def test_discovery_radar_marks_nontrivial_refinement_pass_as_assertion_eligible(self) -> None:
        target = "BEDC.Target.New"
        integrity = {
            "sites": [{
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "chapter_key": "foo",
                "claim_kind": "positiveDiscovery",
                "sources": ["DiscoveryDeltaLedger.classifier_shift"],
                "ledger": "BEDC.Target.Ledger",
                "before_classifiers": ["BEDC.Prior.Old"],
                "declared_new_classifiers": [target],
                "resolution_status": "resolved",
                "provenance": [{
                    "candidate": target,
                    "prior": "BEDC.Prior.Old",
                    "relation": "conjunctive_refinement",
                    "extra_conjunct_count": 2,
                }],
            }],
            "violations": [],
        }
        assert_gate = {
            "asserted_sites": [{
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "target": target,
                "status": "PASS",
                "gates": [{
                    "gate": "G4",
                    "status": "PASS",
                    "details": {
                        "checked_disagreement_supports": [{
                            "support": "BEDC.Target.Support",
                            "module": "BEDC.Target",
                            "axioms": [],
                        }],
                    },
                }],
            }],
        }
        payload = self._radar_payload(integrity, assert_gate=assert_gate)
        candidate = payload["candidates"][0]
        self.assertEqual(candidate["state"], "assertion_eligible")
        self.assertEqual(payload["assertion_eligible_count"], 1)
        self.assertEqual(candidate["refinement_depth"], 2)
        self.assertEqual(
            candidate["disagreement_signal_tier"],
            "kernel_checked_DisagreementSupport",
        )
        self.assertEqual(candidate["valid_use"], "discovery_candidate_surface_and_rank_only")

    def test_discovery_radar_conjectures_signal_without_kernel_witness(self) -> None:
        target = "BEDC.Target.New"
        sieve = {
            "targets": [{
                "target": target,
                "file": "papers/bedc/parts/x.tex",
                "line": 10,
                "region": "FooUp",
                "sources": ["DiscoveryTasteGate"],
                "sieve_profile": {
                    "reason_tags": ["smoke_template_reuse"],
                    "semantic_anchors": ["decode"],
                    "support_targets": ["BEDC.Target.Support"],
                },
            }],
        }
        payload = self._radar_payload({"sites": [], "violations": []}, sieve=sieve)
        candidate = payload["candidates"][0]
        self.assertEqual(candidate["state"], "conjectured")
        self.assertEqual(payload["conjectured_count"], 1)
        self.assertIn("smoke_template_reuse", candidate["risk_tags"])
        self.assertEqual(
            candidate["disagreement_signal_tier"],
            "text_reach_or_semantic_anchor",
        )

    def test_discovery_radar_mines_corpus_reduced_fp_refutation_without_surface(self) -> None:
        headers = {
            "BEDC.Prior.OldClassifier": (
                "def OldClassifier (h0 h1 : BEDC.Core.BHist) : Prop :="
            ),
            "BEDC.Target.NewClassifier": (
                "def NewClassifier (h0 h1 : BEDC.Core.BHist) : Prop :="
            ),
        }
        decls = [
            DeclarationRecord("BEDC.Prior", "lean4/BEDC/Prior.lean", 1, "def",
                              "OldClassifier", "BEDC.Prior.OldClassifier"),
            DeclarationRecord("BEDC.Target", "lean4/BEDC/Target.lean", 1, "def",
                              "NewClassifier", "BEDC.Target.NewClassifier"),
        ]
        scan = LeanSourceScan(decls, [], headers, {}, [])
        fingerprints = {
            "BEDC.Prior.OldClassifier": ExprFingerprint(
                "old", "type", "same", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
            "BEDC.Target.NewClassifier": ExprFingerprint(
                "new", "type", "same", reduced_fingerprint="same",
                canonical_reduced_payload="payload-same",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fingerprints), \
             patch("bedc_ci._run_structural_dna_relations", return_value=([], None)):
            payload = self._radar_payload(
                {"sites": [], "violations": [], "fingerprint_count": 0},
                scan=scan,
                full_corpus_scan=True,
            )
        self.assertEqual(payload["classifier_endpoint_count"], 2)
        self.assertEqual(payload["fingerprint_count"], 2)
        self.assertEqual(payload["source_surface_count"], 0)
        self.assertEqual(payload["corpus_mined_count"], 1)
        self.assertEqual(payload["refuted_count"], 1)
        candidate = payload["candidates"][0]
        self.assertEqual(candidate["target"], "BEDC.Target.NewClassifier")
        self.assertEqual(candidate["state"], "refuted")
        self.assertTrue(candidate["refutation"]["kernel_grounded"])
        self.assertEqual(candidate["provenance"][0]["reduced_fp"], "same")
        self.assertIn("classifier_corpus_canonical_payload_equal", candidate["evidence"])

    def test_discovery_radar_denominators_distinguish_empty_candidate_scan(self) -> None:
        payload = audit_payload(full_radar_scan=True)
        radar = payload["discovery_production_radar"]
        self.assertGreater(radar["classifier_endpoint_count"], 0)
        self.assertIn("fingerprint_count", radar)
        self.assertIn("source_surface_count", radar)
        self.assertIn("corpus_mined_count", radar)
        self.assertIn("corpus_scan_cap", radar)
        self.assertIn("corpus_truncated", radar)

    def test_discovery_radar_conjectured_pool_is_capped_and_logs_drops(self) -> None:
        targets = [f"BEDC.Target.Candidate{i}Classifier" for i in range(105)]
        sieve = {
            "targets": [
                {
                    "target": target,
                    "file": "papers/bedc/parts/x.tex",
                    "line": 10 + idx,
                    "region": "FooUp",
                    "sources": ["DiscoveryTasteGate"],
                    "sieve_profile": {
                        "reason_tags": [f"template smoke variant {idx}"],
                        "semantic_anchors": [f"anchor{idx}"],
                    },
                }
                for idx, target in enumerate(targets)
            ],
        }
        payload = self._radar_payload({"sites": [], "violations": []}, sieve=sieve)
        self.assertEqual(payload["conjectured_count"], 100)
        self.assertEqual(payload["dropped_count"], 5)
        self.assertEqual(payload["conjectured_cap"], 100)
        self.assertEqual(payload["candidate_count"], 100)

    def test_discovery_radar_light_audit_skips_pairwise_full_modes_run_it(self) -> None:
        headers = {
            "BEDC.Prior.OldClassifier": (
                "def OldClassifier (h0 h1 : BEDC.Core.BHist) : Prop :="
            ),
            "BEDC.Target.NewClassifier": (
                "def NewClassifier (h0 h1 : BEDC.Core.BHist) : Prop :="
            ),
        }
        scan = LeanSourceScan([], [], headers, {}, [])
        with patch("bedc_ci._run_structural_dna_expr_fingerprints") as fps, \
             patch("bedc_ci._run_structural_dna_relations") as relations:
            light = self._radar_payload(
                {"sites": [], "violations": [], "fingerprint_count": 0},
                scan=scan,
                full_corpus_scan=False,
            )
        fps.assert_not_called()
        relations.assert_not_called()
        self.assertFalse(light["pairwise_refinement_enabled"])
        self.assertEqual(light["classifier_endpoint_count"], 2)

        fingerprints = {
            "BEDC.Prior.OldClassifier": ExprFingerprint(
                "old", "type", "old", reduced_fingerprint="old",
                canonical_reduced_payload="payload-old",
            ),
            "BEDC.Target.NewClassifier": ExprFingerprint(
                "new", "type", "new", reduced_fingerprint="new",
                canonical_reduced_payload="payload-new",
            ),
        }
        with patch("bedc_ci._run_structural_dna_expr_fingerprints", return_value=fingerprints), \
             patch("bedc_ci._run_structural_dna_relations", return_value=([], None)) as relations:
            full = self._radar_payload(
                {"sites": [], "violations": [], "fingerprint_count": 0},
                scan=scan,
                full_corpus_scan=True,
            )
        relations.assert_called_once()
        self.assertTrue(full["pairwise_refinement_enabled"])

    def test_discovery_radar_subcommand_runs_full_corpus_scan(self) -> None:
        radar_payload = {
            "classifier_endpoint_count": 2,
            "fingerprint_count": 2,
            "candidate_count": 1,
            "refuted_count": 1,
            "assertion_eligible_count": 0,
            "conjectured_count": 0,
            "dropped_count": 0,
            "corpus_mined_count": 1,
            "corpus_scan_cap": 2000,
            "corpus_truncated": False,
            "pairwise_refinement_truncated": False,
            "candidates": [{"state": "refuted", "score": 0, "target": "BEDC.Target", "evidence": []}],
        }
        args = type("Args", (), {"json": False, "verbose": False})()
        with patch("bedc_ci.collect_closurestatus_blocks", return_value=[]), \
             patch("bedc_ci.scan_lean_sources", return_value=LeanSourceScan([], [], {}, {}, [])), \
             patch("bedc_ci.discovery_sieve_payload", return_value={"targets": []}), \
             patch("bedc_ci.discovery_integrity_payload", return_value={"sites": [], "violations": []}), \
             patch("bedc_ci.discovery_assert_gate_payload", return_value={"asserted_sites": []}), \
             patch("bedc_ci.discovery_production_radar_payload", return_value=radar_payload) as radar, \
             redirect_stdout(StringIO()):
            rc = cmd_discovery_radar(args)
        self.assertEqual(rc, 0)
        self.assertTrue(radar.call_args.kwargs["full_corpus_scan"])

    def test_discovery_radar_is_informational_for_audit_exit_code(self) -> None:
        payload = {
            "inventory": {
                "lean_files_scanned": 0,
                "declarations_total": 0,
                "part_labels_total": 0,
                "lean_markers_total": 0,
            },
            "forbidden_constructs": [],
            "forbidden_construct_count": 0,
            "missing_marker_targets": [],
            "missing_marker_targets_new_count": 0,
            "missing_marker_targets_legacy_count": 0,
            "duplicate_part_labels": {},
            "case_collisions": [],
            "case_collisions_new_count": 0,
            "case_collisions_legacy_count": 0,
            "preamble_duplicate_commands": [],
            "preamble_duplicate_commands_new_count": 0,
            "preamble_duplicate_commands_legacy_count": 0,
            "concrete_number_collisions": [],
            "concrete_number_collisions_new_count": 0,
            "concrete_number_collisions_legacy_count": 0,
            "concrete_missing_origin": [],
            "concrete_missing_origin_new_count": 0,
            "concrete_missing_origin_legacy_count": 0,
            "paper_chapter_origin_tags": [],
            "paper_chapter_origin_tags_new_count": 0,
            "paper_chapter_origin_tags_legacy_count": 0,
            "closurestatus_diagnostics": [],
            "closurestatus_diagnostics_new_count": 0,
            "closurestatus_open_errors": [],
            "closurestatus_open_errors_new_count": 0,
            "discovery_integrity_violations_new_count": 0,
            "discovery_assert_gate_failure_count": 0,
            "discovery_nonasserted_hygiene_failure_count": 0,
            "orphan_concrete_subdirs": [],
            "orphan_concrete_subdirs_new_count": 0,
            "leanstmt_debt": {"violations": []},
            "discovery_production_radar": {
                "candidate_count": 1,
                "refuted_count": 1,
                "assertion_eligible_count": 0,
                "conjectured_count": 0,
                "candidates": [{"state": "refuted"}],
            },
        }
        args = type("Args", (), {"json": True, "shape_saturation": False})()
        with patch("bedc_ci.audit_payload", return_value=payload), redirect_stdout(StringIO()):
            rc = cmd_audit(args)
        self.assertEqual(rc, 0)

    def test_plain_audit_uses_light_radar_and_prints_scanned_denominator(self) -> None:
        payload = {
            "inventory": {
                "lean_files_scanned": 0,
                "declarations_total": 0,
                "part_labels_total": 0,
                "lean_markers_total": 0,
            },
            "forbidden_constructs": [],
            "forbidden_construct_count": 0,
            "missing_marker_targets": [],
            "missing_marker_targets_new_count": 0,
            "missing_marker_targets_legacy_count": 0,
            "duplicate_part_labels": {},
            "case_collisions": [],
            "case_collisions_new_count": 0,
            "case_collisions_legacy_count": 0,
            "preamble_duplicate_commands": [],
            "preamble_duplicate_commands_new_count": 0,
            "preamble_duplicate_commands_legacy_count": 0,
            "concrete_number_collisions": [],
            "concrete_number_collisions_new_count": 0,
            "concrete_number_collisions_legacy_count": 0,
            "concrete_missing_origin": [],
            "concrete_missing_origin_new_count": 0,
            "concrete_missing_origin_legacy_count": 0,
            "paper_chapter_origin_tags": [],
            "paper_chapter_origin_tags_new_count": 0,
            "paper_chapter_origin_tags_legacy_count": 0,
            "closurestatus_diagnostics": [],
            "closurestatus_diagnostics_new_count": 0,
            "closurestatus_open_warnings": [],
            "closurestatus_open_warnings_count": 0,
            "closurestatus_open_errors": [],
            "closurestatus_open_errors_new_count": 0,
            "closurestatus_open_errors_legacy_count": 0,
            "discovery_ledger_coverage": {
                "ai_origin_chapter_count": 0,
                "covered_count": 0,
                "missing_count": 0,
                "ledger_declaration_count": 0,
                "stem_warning_count": 0,
                "missing": [],
                "covered": [],
            },
            "mechanical_optout_audit": {
                "finding_count": 0,
                "mechanical_optout_violation_count": 0,
                "findings": [],
            },
            "classifier_shift_quality": {
                "checked_target_count": 0,
                "finding_count": 0,
                "findings": [],
            },
            "discovery_integrity": {
                "declared_discovery_chapter_count": 0,
                "checked_chapter_count": 0,
                "unavailable_count": 0,
                "unresolved_count": 0,
                "semantics": "structural",
                "unresolved": [],
                "unavailable": [],
            },
            "discovery_integrity_violations": [],
            "discovery_integrity_violations_new_count": 0,
            "discovery_integrity_violations_legacy_count": 0,
            "discovery_assert_gate": {
                "asserted_count": 0,
                "status_counts": {},
                "failure_count": 0,
                "conjectured_count": 0,
                "refuted_count": 0,
                "semantics": "assert",
                "asserted_sites": [],
                "failures": [],
                "informational_sites": [],
            },
            "discovery_assert_gate_failure_count": 0,
            "discovery_nonasserted_hygiene": {
                "site_count": 0,
                "failure_count": 0,
                "failures": [],
            },
            "discovery_nonasserted_hygiene_failure_count": 0,
            "orphan_concrete_subdirs": [],
            "orphan_concrete_subdirs_new_count": 0,
            "orphan_concrete_subdirs_legacy_count": 0,
            "theorem_dna_coverage": {
                "covered_count": 0,
                "chapters_total": 0,
                "current_count": 0,
            },
            "theorem_dna_stale": {
                "stale_count": 0,
                "changed_chapters_count": 0,
                "stale": [],
            },
            "leanstmt_debt": {
                "live_sites": [],
                "manifest_entries": [],
                "violations": [],
            },
            "discovery_production_radar": {
                "classifier_endpoint_count": 1743,
                "candidate_count": 1,
                "refuted_count": 1,
                "assertion_eligible_count": 0,
                "conjectured_count": 0,
                "dropped_count": 0,
                "corpus_mined_count": 0,
                "corpus_scan_cap": 2000,
                "corpus_truncated": False,
                "candidates": [{"state": "refuted"}],
            },
        }
        args = type("Args", (), {"json": False, "shape_saturation": False})()
        with patch("bedc_ci.audit_payload", return_value=payload) as audit, redirect_stdout(StringIO()) as out:
            rc = cmd_audit(args)
        self.assertEqual(rc, 0)
        self.assertFalse(audit.call_args.kwargs["full_radar_scan"])
        self.assertIn("scanned=1743", out.getvalue())

    def test_current_repository_discovery_radar_is_present(self) -> None:
        payload = audit_payload()
        self.assertIn("discovery_production_radar", payload)
        radar = payload["discovery_production_radar"]
        self.assertTrue(radar["informational"])
        self.assertEqual(
            radar["semantics"]["valid_use"],
            "discovery_candidate_surface_and_rank_only",
        )


class DiscoveryRefutationPublisherTests(unittest.TestCase):
    def test_refutation_publisher_consumes_only_reduced_fp_twins(self) -> None:
        payload = {
            "candidates": [
                {
                    "state": "refuted",
                    "target": "BEDC.Target.Sound",
                    "refutation": {"kernel_grounded": True},
                    "phase_a": {"reconstruction_priors": ["BEDC.Prior.Old"]},
                    "provenance": [{
                        "relation": "reconstruction",
                        "prior": "BEDC.Prior.Old",
                        "candidate_reduced_fp": "same",
                        "reduced_fp": "same",
                        "canonical_payload": "payload-same",
                        "candidate_canonical_payload": "payload-same",
                        "prior_canonical_payload": "payload-same",
                        "evidence": "canonical_payload_equal",
                    }],
                },
                {
                    "state": "refuted",
                    "target": "BEDC.Target.ZeroRefinementOnly",
                    "refutation": {"kernel_grounded": True},
                    "phase_b": {"zero_refinement_priors": ["BEDC.Prior.Old"]},
                    "provenance": [{
                        "relation": "conjunctive_refinement",
                        "prior": "BEDC.Prior.Old",
                    }],
                },
            ]
        }
        records = refutation_records_from_payload(payload, timestamp="2026-06-02T00:00:00")
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["candidate"], "BEDC.Target.Sound")
        self.assertEqual(
            records[0]["refuted_because"],
            "structural reconstruction (canonical payload equal) of BEDC.Prior.Old",
        )
        self.assertEqual(records[0]["evidence"]["reduced_fp"], "same")
        self.assertEqual(records[0]["evidence"]["evidence"], "canonical_payload_equal")
        self.assertEqual(records[0]["evidence"]["prior"], ["BEDC.Prior.Old"])
        self.assertNotIn("canonical_payload_sha256", records[0]["evidence"])
        self.assertTrue(records[0]["kernel_grounded"])
        self.assertEqual(records[0]["first_seen"], "2026-06-02T00:00:00")
        self.assertNotIn("last_seen", records[0])

    def test_refutation_publisher_dedups_by_candidate_and_prior(self) -> None:
        payload = {
            "candidates": [
                {
                    "state": "refuted",
                    "target": "BEDC.Target.Sound",
                    "refutation": {"kernel_grounded": True},
                    "provenance": [{
                        "relation": "reconstruction",
                        "prior": "BEDC.Prior.Old",
                        "reduced_fp": f"same-{idx}",
                        "canonical_payload": f"payload-{idx}",
                        "candidate_canonical_payload": f"payload-{idx}",
                        "prior_canonical_payload": f"payload-{idx}",
                        "evidence": "canonical_payload_equal",
                    }],
                }
                for idx in range(2)
            ]
        }
        records = refutation_records_from_payload(payload, timestamp="2026-06-02T00:00:00")
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["candidate"], "BEDC.Target.Sound")
        self.assertEqual(records[0]["evidence"]["prior"], ["BEDC.Prior.Old"])
        self.assertNotIn("canonical_payload_sha256", records[0]["evidence"])

    def test_refutation_publisher_preserves_first_seen_without_last_seen(self) -> None:
        existing = [{
            "candidate": "BEDC.Target.Sound",
            "refuted_because": "old",
            "evidence": {"reduced_fp": "old", "evidence": "reduced_fp_only", "prior": ["BEDC.Prior.Old"]},
            "kernel_grounded": True,
            "first_seen": "2026-06-01T00:00:00",
            "last_seen": "2026-06-01T01:00:00",
        }]
        current = [{
            "candidate": "BEDC.Target.Sound",
            "refuted_because": "structural reconstruction (canonical payload equal) of BEDC.Prior.Old",
            "evidence": {
                "reduced_fp": "same",
                "evidence": "canonical_payload_equal",
                "prior": ["BEDC.Prior.Old"],
            },
            "kernel_grounded": True,
            "first_seen": "2026-06-02T00:00:00",
        }]
        records = merge_records(existing, current, timestamp="2026-06-02T00:00:00")
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["first_seen"], "2026-06-01T00:00:00")
        self.assertEqual(records[0]["evidence"]["evidence"], "canonical_payload_equal")
        self.assertEqual(records[0]["evidence"]["reduced_fp"], "same")
        self.assertNotIn("last_seen", records[0])

    def test_refutation_publisher_replace_semantics_purges_absent_entries(self) -> None:
        existing = [
            {
                "candidate": "BEDC.Target.Sound",
                "refuted_because": "old",
                "evidence": {
                    "reduced_fp": "old",
                    "evidence": "reduced_fp_only",
                    "prior": ["BEDC.Prior.Old"],
                },
                "kernel_grounded": True,
                "first_seen": "2026-06-01T00:00:00",
            },
            {
                "candidate": "BEDC.Target.Absent",
                "refuted_because": "old false positive",
                "evidence": {
                    "reduced_fp": "absent",
                    "evidence": "reduced_fp_only",
                    "prior": ["BEDC.Prior.Old"],
                },
                "kernel_grounded": True,
                "first_seen": "2026-06-01T00:00:00",
            },
        ]
        current = [{
            "candidate": "BEDC.Target.Sound",
            "refuted_because": "structural reconstruction (canonical payload equal) of BEDC.Prior.Old",
            "evidence": {
                "reduced_fp": "same",
                "evidence": "canonical_payload_equal",
                "prior": ["BEDC.Prior.Old"],
            },
            "kernel_grounded": True,
            "first_seen": "2026-06-02T00:00:00",
        }]
        records = merge_records(existing, current, timestamp="2026-06-02T00:00:00")
        self.assertEqual([record["candidate"] for record in records], ["BEDC.Target.Sound"])
        self.assertEqual(records[0]["first_seen"], "2026-06-01T00:00:00")
        self.assertEqual(records[0]["evidence"]["evidence"], "canonical_payload_equal")

    def test_refutation_publisher_content_signature_detects_evidence_change(self) -> None:
        old = [{
            "candidate": "BEDC.Target.Sound",
            "refuted_because": "structural reconstruction (canonical payload equal) of BEDC.Prior.Old",
            "evidence": {
                "reduced_fp": "old",
                "evidence": "reduced_fp_only",
                "prior": ["BEDC.Prior.Old"],
            },
            "kernel_grounded": True,
            "first_seen": "2026-06-01T00:00:00",
        }]
        new = [{
            **old[0],
            "evidence": {
                "reduced_fp": "same",
                "evidence": "canonical_payload_equal",
                "prior": ["BEDC.Prior.Old"],
            },
        }]
        self.assertNotEqual(ledger_content_signature(old), ledger_content_signature(new))

    def test_structural_dna_ensure_build_rebuilds_when_source_newer(self) -> None:
        import structural_dna_build  # type: ignore[import-not-found]
        from subprocess import CompletedProcess

        calls: list[str] = []
        with patch.object(structural_dna_build, "structural_dna_source_newer_than_exe", return_value=True), \
                patch.object(
                    structural_dna_build,
                    "run_lake_build",
                    return_value=CompletedProcess(["lake", "build", "structural_dna"], 0, "", ""),
                ) as build, \
                patch.object(
                    structural_dna_build,
                    "structural_dna_probe",
                    return_value=CompletedProcess(
                        ["structural_dna"],
                        0,
                        json.dumps({
                            "BEDC.StructuralDna.TestTargets.AlphaLamA": {
                                "canonical_reduced_payload": "payload"
                            }
                        }),
                        "",
                    ),
                ):
            reason = structural_dna_build.ensure_structural_dna_build(append_log=calls.append, label="test")
        self.assertIsNone(reason)
        build.assert_called_once()

    def test_structural_dna_ensure_build_retries_empty_canonical_payload(self) -> None:
        import structural_dna_build  # type: ignore[import-not-found]
        from subprocess import CompletedProcess

        empty = CompletedProcess(["structural_dna"], 0, json.dumps({
            "BEDC.StructuralDna.TestTargets.AlphaLamA": {"canonical_reduced_payload": ""}
        }), "")
        filled = CompletedProcess(["structural_dna"], 0, json.dumps({
            "BEDC.StructuralDna.TestTargets.AlphaLamA": {"canonical_reduced_payload": "payload"}
        }), "")
        with patch.object(structural_dna_build, "structural_dna_source_newer_than_exe", return_value=False), \
                patch.object(
                    structural_dna_build,
                    "run_lake_build",
                    return_value=CompletedProcess(["lake", "build", "structural_dna"], 0, "", ""),
                ) as build, \
                patch.object(structural_dna_build, "structural_dna_probe", side_effect=[empty, filled]):
            reason = structural_dna_build.ensure_structural_dna_build(label="test")
        self.assertIsNone(reason)
        build.assert_called_once()

    def test_structural_dna_build_lock_serializes_callers(self) -> None:
        import structural_dna_build  # type: ignore[import-not-found]

        entered: list[str] = []
        second_attempted = threading.Event()
        first_can_release = threading.Event()
        second_entered = threading.Event()
        errors: list[BaseException] = []

        def first() -> None:
            try:
                with structural_dna_build.structural_dna_build_lock(label="first", timeout=5):
                    entered.append("first")
                    second_attempted.wait(2)
                    time.sleep(0.1)
                    self.assertFalse(second_entered.is_set())
                    first_can_release.set()
            except BaseException as exc:
                errors.append(exc)

        def second() -> None:
            try:
                second_attempted.set()
                with structural_dna_build.structural_dna_build_lock(label="second", timeout=5):
                    entered.append("second")
                    second_entered.set()
            except BaseException as exc:
                errors.append(exc)

        with TemporaryDirectory() as tmp, \
                patch.object(structural_dna_build, "STRUCTURAL_DNA_BUILD_LOCK", Path(tmp) / "build.lock"):
            first_thread = threading.Thread(target=first)
            second_thread = threading.Thread(target=second)
            first_thread.start()
            deadline = time.monotonic() + 2
            while entered != ["first"] and time.monotonic() < deadline and not errors:
                time.sleep(0.01)
            self.assertEqual(entered, ["first"])
            second_thread.start()
            self.assertTrue(first_can_release.wait(2))
            first_thread.join(2)
            second_thread.join(2)
            self.assertFalse(first_thread.is_alive())
            self.assertFalse(second_thread.is_alive())
            if errors:
                raise errors[0]
            self.assertEqual(entered, ["first", "second"])

    def test_discovery_gate_evolver_exact_keys_do_not_collapse_same_bucket(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "witnesses.json"
            path.write_text(json.dumps({
                "schema": "bedc.discovery_gate_witness_registry",
                "witnesses": [
                    {
                        "id": "one",
                        "kind": "reconstruction",
                        "pattern": {
                            "target": "BEDC.Target.One",
                            "prior": "BEDC.Prior.Old",
                            "canonical_payload": "payload-same",
                        },
                    },
                    {
                        "id": "two",
                        "kind": "reconstruction",
                        "pattern": {
                            "target": "BEDC.Target.Two",
                            "prior": "BEDC.Prior.Old",
                            "canonical_payload": "payload-same",
                        },
                    },
                ],
            }), encoding="utf-8")
            with patch.object(discovery_gate_evolver, "_BEDC_CI", sys.modules["bedc_ci"]):
                exact_keys, count, cap = discovery_gate_evolver.registry_exact_keys_and_count(path)
        self.assertEqual(count, 2)
        self.assertGreater(cap, count)
        self.assertIn(("BEDC.Target.One", "BEDC.Prior.Old", "payload-same"), exact_keys)
        self.assertIn(("BEDC.Target.Two", "BEDC.Prior.Old", "payload-same"), exact_keys)

    def test_discovery_gate_evolver_capacity_fails_closed_near_cap(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        with self.assertRaises(discovery_gate_evolver.FailClosed):
            discovery_gate_evolver.ensure_registry_capacity(1900, 2000, 1)

    def test_discovery_gate_evolver_daemon_processes_before_sleep(self) -> None:
        import discovery_gate_evolver  # type: ignore[import-not-found]

        events: list[str] = []

        def fake_sleep(_seconds: float) -> None:
            events.append("sleep")
            raise KeyboardInterrupt

        with patch.object(sys, "argv", ["discovery_gate_evolver.py", "--interval", "999"]), \
                patch.object(discovery_gate_evolver, "pid_lock", return_value=nullcontext()), \
                patch.object(discovery_gate_evolver, "append_log", side_effect=events.append), \
                patch.object(discovery_gate_evolver, "run_once", side_effect=lambda _args: events.append("run") or 0), \
                patch.object(discovery_gate_evolver.time, "sleep", side_effect=fake_sleep):
            with self.assertRaises(KeyboardInterrupt):
                discovery_gate_evolver.main()
        self.assertIn("[gate-evolver] daemon start interval=999s", events)
        self.assertLess(events.index("run"), events.index("sleep"))


if __name__ == "__main__":
    unittest.main(verbosity=2)

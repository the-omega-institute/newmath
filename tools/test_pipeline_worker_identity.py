from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from pipeline_worker_identity import (
    legacy_branch_kind,
    legacy_ticket_kind,
    legacy_worktree_kind,
    new_worker_lease,
    parse_new_worktree_name,
    sanitize_slug,
)


class PipelineWorkerIdentityTests(unittest.TestCase):
    def test_formalize_identity_schema(self) -> None:
        root = Path("/tmp/worktrees")
        lease = new_worker_lease(
            "formalize",
            "BEDC.Derived/FooUp",
            lease_id="wabc1234",
            display_ordinal=77,
            worktree_dir=root,
        )

        self.assertEqual(lease.semantic_slug, "bedc-derived-fooup")
        self.assertEqual(lease.branch, "formalize-bedc-derived-fooup-wabc1234")
        self.assertEqual(lease.worktree_name, "formalize_bedc_derived_fooup_wabc1234")
        self.assertEqual(lease.worktree, root / "formalize_bedc_derived_fooup_wabc1234")
        self.assertEqual(lease.commit_prefix, "formalize-bedc-derived-fooup-wabc1234:")
        self.assertEqual(lease.holder, "formalize-bedc-derived-fooup-wabc1234")
        self.assertEqual(lease.display_ordinal, 77)

    def test_paper_identity_schema(self) -> None:
        lease = new_worker_lease(
            "paper-revise",
            "closure mark",
            lease_id="wxyz9876",
        )

        self.assertEqual(lease.branch, "paper-revise-closure-mark-wxyz9876")
        self.assertEqual(lease.worktree_name, "paper_revise_closure_mark_wxyz9876")
        self.assertEqual(lease.commit_prefix, "paper-revise-closure-mark-wxyz9876:")
        self.assertEqual(lease.holder, "paper-revise-closure-mark-wxyz9876")

    def test_forbidden_iteration_shapes_rejected(self) -> None:
        for value in ("R12", "P9", "round-12", "paper-7"):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    sanitize_slug(value, fallback="formalize")

        with self.assertRaises(ValueError):
            new_worker_lease("formalize", "codex-R12", lease_id="wabc1234")
        with self.assertRaises(ValueError):
            new_worker_lease("paper-revise", "Round trip", lease_id="wabc1234")

    def test_metadata_round_trip(self) -> None:
        lease = new_worker_lease("formalize", "foo", lease_id="wabc1234")
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "identity.json"
            lease.write_metadata(path)
            data = json.loads(path.read_text(encoding="utf-8"))

        self.assertEqual(data["kind"], "formalize")
        self.assertEqual(data["semantic_slug"], "foo")
        self.assertEqual(data["lease_id"], "wabc1234")
        self.assertEqual(data["holder"], "formalize-foo-wabc1234")

    def test_new_and_legacy_matchers(self) -> None:
        self.assertEqual(
            parse_new_worktree_name("formalize_foo_bar_wabc1234"),
            ("formalize", "foo-bar", "wabc1234"),
        )
        self.assertEqual(
            parse_new_worktree_name("paper_revise_foo_wxyz9876"),
            ("paper-revise", "foo", "wxyz9876"),
        )
        self.assertEqual(legacy_worktree_kind("round_R42"), ("formalize", 42))
        self.assertEqual(legacy_worktree_kind("paper_P17"), ("paper-revise", 17))
        self.assertEqual(legacy_branch_kind("codex-R42"), ("formalize", 42))
        self.assertEqual(legacy_branch_kind("paper-P17"), ("paper-revise", 17))
        self.assertEqual(legacy_ticket_kind("R42_123.json"), ("formalize", 42))
        self.assertEqual(legacy_ticket_kind("P17_123.json"), ("paper-revise", 17))


if __name__ == "__main__":
    unittest.main()

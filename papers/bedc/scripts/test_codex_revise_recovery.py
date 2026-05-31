from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "codex_revise.py"
TOOLS_PATH = REPO_ROOT / "tools"
if str(TOOLS_PATH) not in sys.path:
    sys.path.insert(0, str(TOOLS_PATH))


def load_codex_revise():
    spec = importlib.util.spec_from_file_location("codex_revise_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cr = load_codex_revise()


class PaperRecoveryTicketTests(unittest.TestCase):
    def test_recovery_request_writes_semantic_ticket_discovered_by_consumer_matcher(self):
        with tempfile.TemporaryDirectory() as td:
            queue = Path(td) / "queue"
            dead = queue / "dead"
            lease = cr.new_worker_lease("paper-revise", "foo", lease_id="wxyz9876")
            wt = cr.WorktreeInfo(
                path=Path(td) / "worktree",
                branch=lease.branch,
                round_number=17,
                base_sha="abc123",
                lease=lease,
            )
            original_queue = cr.RECOVERY_QUEUE_DIR
            original_dead = cr.RECOVERY_DEAD_DIR
            original_time = cr.time.time
            try:
                cr.RECOVERY_QUEUE_DIR = queue
                cr.RECOVERY_DEAD_DIR = dead
                cr.time.time = lambda: 12345

                cr.request_recovery(wt)

                tickets = sorted(
                    p.name
                    for p in queue.iterdir()
                    if p.is_file()
                    and p.suffix == ".json"
                    and cr.is_recovery_ticket(p.name, "paper-revise")
                )
                self.assertEqual(tickets, ["paper_revise_foo_wxyz9876_12345.json"])
                self.assertTrue(cr.is_recovery_ticket("P17_12345.json", "paper-revise"))
                self.assertNotIn("wxyz9876_wxyz9876", tickets[0])
            finally:
                cr.RECOVERY_QUEUE_DIR = original_queue
                cr.RECOVERY_DEAD_DIR = original_dead
                cr.time.time = original_time


if __name__ == "__main__":
    unittest.main()

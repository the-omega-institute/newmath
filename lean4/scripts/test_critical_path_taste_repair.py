#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import os
import sys
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[2]
CRITICAL_PATH = REPO_ROOT / "lean4" / "scripts" / "critical_path.py"
FORMALIZE_PATH = REPO_ROOT / "lean4" / "scripts" / "codex_formalize.py"
TOOLS_PATH = REPO_ROOT / "tools"
if str(TOOLS_PATH) not in sys.path:
    sys.path.insert(0, str(TOOLS_PATH))


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class CriticalPathTasteRepairTests(unittest.TestCase):
    def test_taste_repair_critical_path_disabled_does_not_read_audit(self) -> None:
        cp = load_module(CRITICAL_PATH, "critical_path_taste_disabled")
        with mock.patch.dict(os.environ, {"BEDC_TASTE_REPAIR_ENABLED": "0"}, clear=False), \
            mock.patch.object(cp.subprocess, "run") as run_mock:
            payload = cp._get_taste_repair_payload()
            targets = cp.compute_taste_repair_targets(payload)

        self.assertFalse(payload["enabled"])
        self.assertEqual(targets, [])
        run_mock.assert_not_called()

    def test_taste_repair_critical_path_enabled_maps_violations_to_low_priority_targets(self) -> None:
        cp = load_module(CRITICAL_PATH, "critical_path_taste_enabled")
        payload = {
            "available": True,
            "enabled": True,
            "violation_count": 1,
            "violations": [
                {
                    "target": "BEDC.Derived.CompactUp.CompactCarrier",
                    "prior": "BEDC.Derived.BoolUp.BoolCarrier",
                    "target_domain": "Compact",
                    "prior_domain": "Bool",
                    "obligation_id": "structural-distinctness",
                    "criterion": "carrier_faithfulness.cross_domain_canonical_payload_distinct",
                }
            ],
        }
        with mock.patch.dict(os.environ, {"BEDC_TASTE_REPAIR_ENABLED": "1"}, clear=False), \
            mock.patch.object(cp, "_current_worker_slice", return_value=(0, 1)), \
            mock.patch.object(cp, "_claim_top_with_cooldown", side_effect=lambda rows: rows):
            targets = cp.compute_taste_repair_targets(payload)

        self.assertEqual(len(targets), 1)
        target = targets[0]
        self.assertEqual(target["kind"], "taste_repair")
        self.assertEqual(target["carrier"], "BEDC.Derived.CompactUp.CompactCarrier")
        self.assertEqual(target["prior"], "BEDC.Derived.BoolUp.BoolCarrier")
        self.assertEqual(target["dispatch_source"], "taste_repair_top")
        self.assertEqual(target["priority"], "low")
        self.assertEqual(target["target_file"], "lean4/BEDC/Derived/CompactUp.lean")

    def test_taste_repair_formalize_disabled_rejects_lane(self) -> None:
        cf = load_module(FORMALIZE_PATH, "codex_formalize_taste_disabled")
        with mock.patch.dict(os.environ, {"BEDC_TASTE_REPAIR_ENABLED": "0"}, clear=False):
            self.assertFalse(cf.taste_repair_enabled())
        self.assertTrue(cf._is_taste_repair_targets([
            {"kind": "taste_repair", "carrier": "BEDC.Derived.CompactUp.CompactCarrier"}
        ]))
        self.assertEqual(
            cf._target_id({
                "kind": "taste_repair",
                "carrier": "BEDC.Derived.CompactUp.CompactCarrier",
            }),
            "taste_repair:BEDC.Derived.CompactUp.CompactCarrier",
        )


if __name__ == "__main__":
    unittest.main()

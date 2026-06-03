#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import sys
import types
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
    def test_taste_repair_payload_is_read_unconditionally(self) -> None:
        cp = load_module(CRITICAL_PATH, "critical_path_taste_payload")
        fake_bedc_ci = types.SimpleNamespace(
            audit_payload=lambda full_radar_scan=False: {
                "taste_meta_gate": {
                    "violation_count": 1,
                    "obligation_count": 2,
                    "violations": [
                        {
                            "target": "BEDC.Derived.CompactUp.CompactCarrier",
                            "prior": "BEDC.Derived.BoolUp.BoolCarrier",
                        }
                    ],
                }
            }
        )

        with mock.patch.dict(sys.modules, {"bedc_ci": fake_bedc_ci}):
            payload = cp._get_taste_repair_payload()

        self.assertTrue(payload["enabled"])
        self.assertTrue(payload["available"])
        self.assertEqual(payload["violation_count"], 1)
        self.assertEqual(len(payload["violations"]), 1)

    def test_taste_repair_critical_path_maps_violations_to_low_priority_targets(self) -> None:
        cp = load_module(CRITICAL_PATH, "critical_path_taste_targets")
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
        with mock.patch.object(cp, "_current_worker_slice", return_value=(0, 1)), \
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

    def test_taste_repair_weight_is_present_and_below_regular_lean_sources(self) -> None:
        cp = load_module(CRITICAL_PATH, "critical_path_taste_weight")
        supply_lean = {
            "top": 5,
            "sieve_clearance_top": 5,
            "discovery_candidate_top": 5,
            "formal_axis_top": 5,
            "unformalized_top": 5,
            "carrier_isomorphism_capstone": 5,
            "taste_repair_top": 5,
        }
        supply_paper = {
            "top": 5,
        }
        lean_base = dict(cp._LEAN_BASE_WEIGHTS)
        lean_base["taste_repair_top"] = cp.TASTE_REPAIR_WEIGHT

        weights = cp._compute_dispatch_weights(
            supply_lean,
            supply_paper,
            {},
            lean_base,
            {"top": 1.0},
        )["lean"]["weights"]

        self.assertIn("taste_repair_top", weights)
        self.assertGreater(weights["taste_repair_top"], 0)
        for source in cp._LEAN_BASE_WEIGHTS:
            self.assertLess(weights["taste_repair_top"], weights[source])

    def test_taste_repair_formalize_lane_identity_is_always_available(self) -> None:
        cf = load_module(FORMALIZE_PATH, "codex_formalize_taste_identity")
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

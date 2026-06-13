from __future__ import annotations

import argparse
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import discovery_pipeline_daemon as pipeline
import discovery_refutation_publisher as publisher


def sample_radar_payload() -> dict:
    return {
        "classifier_endpoint_count": 1,
        "fingerprint_count": 1,
        "candidate_count": 1,
        "refuted_count": 1,
        "candidates": [
            {
                "target": "BEDC.Discovery.Candidate",
                "state": "refuted",
                "refutation": {"kernel_grounded": True},
                "provenance": [
                    {
                        "relation": "reconstruction",
                        "kernel_grounded": True,
                        "evidence": "canonical_payload_equal",
                        "prior": "BEDC.Discovery.Prior",
                        "candidate_canonical_payload": "payload",
                        "prior_canonical_payload": "payload",
                        "canonical_payload": "payload",
                        "reduced_fp": "fp",
                    }
                ],
            }
        ],
    }


class DiscoveryRadarPayloadReuseTests(unittest.TestCase):
    def test_publisher_uses_supplied_payload_without_radar_subprocess(self) -> None:
        payload = sample_radar_payload()
        with tempfile.TemporaryDirectory() as td, \
                patch.object(publisher, "PUBLISH_WORKTREE", Path(td)), \
                patch.object(publisher, "ensure_publish_worktree", return_value=True), \
                patch.object(publisher, "ensure_structural_dna_build", return_value=None), \
                patch.object(publisher, "load_radar_payload") as load_radar_payload, \
                patch.object(publisher, "commit_and_maybe_push", return_value=(True, "ok")), \
                patch.object(publisher, "append_log"), \
                patch.object(publisher, "print"):
            load_radar_payload.side_effect = AssertionError("unexpected radar subprocess")

            self.assertTrue(publisher.run_once(no_push=True, radar_payload=payload))

            load_radar_payload.assert_not_called()

    def test_publisher_loads_radar_payload_when_not_supplied(self) -> None:
        payload = sample_radar_payload()
        with tempfile.TemporaryDirectory() as td, \
                patch.object(publisher, "PUBLISH_WORKTREE", Path(td)), \
                patch.object(publisher, "ensure_publish_worktree", return_value=True), \
                patch.object(publisher, "ensure_structural_dna_build", return_value=None), \
                patch.object(publisher, "load_radar_payload", return_value=payload) as load_radar_payload, \
                patch.object(publisher, "commit_and_maybe_push", return_value=(True, "ok")), \
                patch.object(publisher, "append_log"), \
                patch.object(publisher, "print"):

            self.assertTrue(publisher.run_once(no_push=True))

            load_radar_payload.assert_called_once_with()

    def test_pipeline_passes_successful_radar_payload_to_publisher(self) -> None:
        payload = sample_radar_payload()
        args = argparse.Namespace(
            no_push=True,
            proven_pseudos="/tmp/proven-pseudos.jsonl",
        )
        publisher_run_once = Mock(return_value=True)

        with patch.object(pipeline, "append_log"), \
                patch.object(pipeline, "ensure_structural_dna_build", return_value=None), \
                patch.object(pipeline, "jsonl_count", return_value=0), \
                patch.object(pipeline.radar, "run_once", return_value={
                    "scanned": 1,
                    "fingerprints": 1,
                    "_radar_payload": payload,
                }), \
                patch.object(pipeline.publisher, "run_once", publisher_run_once), \
                patch.object(pipeline, "make_generator_args", return_value=object()), \
                patch.object(pipeline.generator, "run_once", return_value={"status": "ok"}), \
                patch.object(pipeline, "make_evolver_args", return_value=object()), \
                patch.object(pipeline.evolver, "run_once", return_value=0), \
                patch("builtins.print"):

            summary = pipeline.run_cycle(args)

        self.assertTrue(summary["ok"])
        publisher_run_once.assert_called_once_with(no_push=True, radar_payload=payload)

    def test_pipeline_does_not_pass_degraded_radar_payload_to_publisher(self) -> None:
        payload = sample_radar_payload()
        args = argparse.Namespace(
            no_push=True,
            proven_pseudos="/tmp/proven-pseudos.jsonl",
        )
        publisher_run_once = Mock(return_value=True)

        with patch.object(pipeline, "append_log"), \
                patch.object(pipeline, "ensure_structural_dna_build", return_value=None), \
                patch.object(pipeline, "jsonl_count", return_value=0), \
                patch.object(pipeline.radar, "run_once", return_value={
                    "scanned": 0,
                    "fingerprints": 0,
                    "degraded": True,
                    "_radar_payload": payload,
                }), \
                patch.object(pipeline.publisher, "run_once", publisher_run_once), \
                patch.object(pipeline, "make_generator_args", return_value=object()), \
                patch.object(pipeline.generator, "run_once", return_value={"status": "ok"}), \
                patch.object(pipeline, "make_evolver_args", return_value=object()), \
                patch.object(pipeline.evolver, "run_once", return_value=0), \
                patch("builtins.print"):

            summary = pipeline.run_cycle(args)

        self.assertTrue(summary["ok"])
        publisher_run_once.assert_called_once_with(no_push=True, radar_payload=None)


if __name__ == "__main__":
    unittest.main()

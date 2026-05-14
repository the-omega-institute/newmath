#!/usr/bin/env python3
"""QA guard for inspiration-only BEDC landing paths.

Vision and conjecture files may inform candidate discovery, but automated
BOARD and Stage 2 writeback lanes must not land theorem-shaped content there.
"""

from __future__ import annotations

import auto_discovery
import candidate_inbox
import killo_golden_writeback
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BRIDGE_DIR = REPO_ROOT / "tools" / "automath_newmath_bridge"
sys.path.insert(0, str(BRIDGE_DIR))
import bridge_to_bedc_board  # type: ignore  # noqa: E402


def _candidate(path: str) -> dict:
    return {
        "title": f"QA inspiration-only landing {path.rsplit('/', 1)[-1]}",
        "claim": (
            "If an inspiration-only path appears as a local input, the candidate "
            "must remain review evidence and must not become an executable BOARD "
            "writeback target."
        ),
        "local_inputs": [path],
        "fit_score": 9,
        "novelty": 9,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
    }


def main() -> int:
    paths = [
        "papers/bedc/parts/visions/metacic_open_problems.tex",
        "papers/bedc/parts/conjectures/finite_bhist_injection_admits_stdbridge.tex",
    ]
    file_lookup = candidate_inbox._paper_file_lookup()
    labels = candidate_inbox._paper_labels(file_lookup)
    existing_titles: set[str] = set()
    seen_titles: set[str] = set()

    for path in paths:
        candidate = _candidate(path)
        reason = candidate_inbox._rejection_reason(
            candidate,
            source="qa",
            existing_titles=existing_titles,
            seen_titles=seen_titles,
            file_lookup=file_lookup,
            existing_labels=labels,
            fit_threshold=7,
            novelty_threshold=6,
        )
        assert reason.startswith("inspiration_only_not_board_landing:"), reason

        normalized = auto_discovery._for_board_spawn(candidate, mode="qa")
        assert normalized["local_inputs"] == [], normalized["local_inputs"]
        assert path in normalized.get("rationale", ""), normalized.get("rationale", "")

        target = killo_golden_writeback._resolve_target_tex(path)
        assert target is None, target

    bridge_record = {
        "source_repo": "the-omega-institute/automath",
        "source_branch_or_ref": "origin/main",
        "source_commit": "abc123",
        "source_path": "automath/some/theorem.lean",
        "source_artifact_kind": "lean_theorem",
        "destination_path": "tools/automath_newmath_bridge/review_packets/signal.json",
        "bridge_direction": "automath_to_newmath",
        "gate_status": "gate_passed",
        "readiness": "ready_for_local_packet",
        "destination_repo": "the-omega-institute/newmath",
        "priority": 90,
        "evidence_summary": ["source signal is useful but has no BEDC-native landing yet"],
    }
    bridge_candidate = bridge_to_bedc_board._candidate(
        bridge_record,
        "tools/automath_newmath_bridge/review_packets/signal.json",
    )
    assert bridge_candidate["local_inputs"] == [], bridge_candidate["local_inputs"]
    assert bridge_candidate["landing_kind"] == "reject", bridge_candidate["landing_kind"]
    assert (
        "tools/automath_newmath_bridge/review_packets/signal.json"
        in bridge_candidate["review_metadata_inputs"]
    )
    reason = candidate_inbox._rejection_reason(
        bridge_candidate,
        source="automath_newmath_bridge",
        existing_titles=existing_titles,
        seen_titles=seen_titles,
        file_lookup=file_lookup,
        existing_labels=labels,
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert reason == "external_signal_landing_reject", reason

    landing_record = dict(bridge_record)
    landing_record["paper_files"] = [
        "papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex"
    ]
    landing_candidate = bridge_to_bedc_board._candidate(
        landing_record,
        "tools/automath_newmath_bridge/review_packets/signal.json",
    )
    assert landing_candidate["local_inputs"] == [
        "papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex"
    ], landing_candidate["local_inputs"]
    assert landing_candidate["landing_kind"] == "existing_chapter_lemma", landing_candidate["landing_kind"]
    assert not any(
        path.startswith("tools/automath_newmath_bridge/review_packets/")
        for path in landing_candidate["local_inputs"]
    )

    print("qa_vision_landing_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

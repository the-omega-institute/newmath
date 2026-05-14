#!/usr/bin/env python3
"""QA guard for inspiration-only BEDC landing paths.

Vision and conjecture files may inform candidate discovery, but automated
BOARD and Stage 2 writeback lanes must not land theorem-shaped content there.
"""

from __future__ import annotations

import auto_discovery
import candidate_inbox
import killo_golden_writeback


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

    print("qa_vision_landing_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

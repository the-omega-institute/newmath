#!/usr/bin/env python3
"""Smoke tests for the BEDC structural relation miner."""

from __future__ import annotations

import structural_relation_miner


def main() -> int:
    assert structural_relation_miner.MAX_FILE_LINES <= 660
    candidates = structural_relation_miner.generate_candidates(limit=12)
    assert candidates, "expected at least one structural relation candidate"
    for cand in candidates:
        assert cand.get("source") == "research_lane:structural_relation_miner"
        existing_titles = structural_relation_miner.board_archive.existing_target_titles(
            include_archive=True
        )
        assert cand.get("title", "").strip().lower() not in existing_titles
        assert cand.get("landing_kind") == "existing_chapter_lemma"
        assert cand.get("tastegate_mode") == "existing_chapter"
        assert cand.get("relation_family") in {
            "forgetful_projection",
            "equivalence_completion",
            "mirror_dual",
            "bridge_cut",
            "bisimulation",
            "classifier_alignment",
        }
        assert cand.get("equality_kind") in {
            "none",
            "equivalent",
            "bisimilar",
            "substrate_mirror",
        }
        assert cand.get("interpretation_kind") in {
            "none",
            "interpretation",
            "faithful_embedding",
            "quotient_projection",
            "substrate_mirror",
        }
        local_inputs = cand.get("local_inputs") or []
        assert local_inputs, cand
        for rel in local_inputs:
            assert rel.startswith("papers/bedc/parts/")
            assert "/visions/" not in rel
            assert "/conjectures/" not in rel
            assert not rel.endswith("00_concrete_instance_macros.tex")
            assert not rel.endswith("00_large_model_macros.tex")
        rationale = str(cand.get("rationale") or "")
        assert "why_not_parameter_echo" in rationale
        assert "minimal_bedc_native_landing" in rationale
    print("test_structural_relation_miner: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

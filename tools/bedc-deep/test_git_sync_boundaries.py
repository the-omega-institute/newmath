#!/usr/bin/env python3
"""Static regression checks for BEDC paper-native Git sync boundaries."""

from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
SUPERVISOR = SCRIPT_DIR / "supervisor.py"
AUTO_DISCOVERY = SCRIPT_DIR / "auto_discovery.py"
PROMPTS_DIR = SCRIPT_DIR / "prompts"


def _text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_supervisor_does_not_clear_stop_file() -> None:
    text = _text(SUPERVISOR)
    assert "STOP_FILE present; supervisor not starting" in text
    assert "STOP_FILE.unlink()" not in text


def test_supervisor_runs_gated_dev_sync_resolver() -> None:
    text = _text(SUPERVISOR)
    start = text.index("def git_sync_dev()")
    end = text.index("\ndef trigger_probe", start)
    body = text[start:end]
    assert "origin/auto-dev" in body or "dev_sync_resolver" in body
    assert "DEV_SYNC_RESOLVER" in body
    assert "subprocess.run" in body
    assert '["python3", str(DEV_SYNC_RESOLVER)]' in body
    assert "Safety lives in dev_sync_resolver's path protection" in body


def test_supervisor_keeps_discovery_children_single_sync_entrypoint() -> None:
    text = _text(SUPERVISOR)
    for name in (
        "trigger_probe",
        "trigger_curriculum_probe",
        "trigger_paper_review",
        "trigger_curator",
    ):
        start = text.index(f"def {name}")
        try:
            end = text.index("\ndef ", start + 1)
        except ValueError:
            end = len(text)
        body = text[start:end]
        assert "cmd.append(\"--no-dev-sync\")" in body, name


def test_supervisor_defaults_to_continuous_auto_dev_sync() -> None:
    text = _text(SUPERVISOR)
    assert "DEFAULT_DEV_SYNC_COOLDOWN_MINUTES = 15" in text
    assert "dev_sync_enabled = not bool(args.no_dev_sync)" in text
    assert "git_sync_dev()" in text
    assert "--no-dev-sync" in text
    assert "Disable BEDC sync from origin/auto-dev" in text


def test_supervisor_defaults_to_paper_native_discovery() -> None:
    text = _text(SUPERVISOR)
    assert "DEFAULT_ALLOW_LEAN_ADJACENT_DISCOVERY = False" in text
    assert "--allow-lean-adjacent-discovery" in text
    assert "paper-native supervisor defaults forbid" in text
    assert "Lean-adjacent discovery" in text
    assert "oracle_board_refill" in text
    assert "paper_review remain enabled" in text


def test_supervisor_has_hard_branch_guard() -> None:
    text = _text(SUPERVISOR)
    assert 'REQUIRED_BRANCH = "bedc-claim-packet-pipeline"' in text
    assert "def assert_required_branch()" in text
    assert "branch guard: refusing to run" in text
    start = text.index("def main()")
    body = text[start:]
    assert "if not assert_required_branch():" in body


def test_supervisor_refill_can_recover_from_stale_circuit_breaker() -> None:
    text = _text(SUPERVISOR)
    start = text.index("def trigger_oracle_board_refill()")
    end = text.index("\ndef run_loning_watch", start)
    body = text[start:end]
    assert "dispatch_ready_poll_agents" in body
    assert "--ignore-refill-circuit-breaker" in body
    assert "ignoring stale refill circuit breaker" in body


def test_supervisor_keeps_board_state_files_local_only() -> None:
    text = _text(SUPERVISOR)
    start = text.index("def commit_and_push_if_changed()")
    end = text.index("\n\n# ---------------------------------------------------------------------------\n# PI agent review", start)
    body = text[start:end]
    assert '"tools/bedc-deep/BOARD.md"' in body
    assert '"tools/bedc-deep/BOARD.completed.md"' in body
    assert "local_only_state_files" in body
    assert "if path not in local_only_state_files" in body
    assert "local-only BOARD state files" in body


def test_auto_discovery_dev_sync_is_opt_in_and_path_guarded() -> None:
    text = _text(AUTO_DISCOVERY)
    assert "dev_sync_enabled = bool(getattr(args, \"dev_sync\", False))" in text
    assert "path.startswith(\"lean4/\")" in text
    assert "papers/bedc/main.tex" in text
    assert "papers/bedc/preamble.tex" in text
    assert "[discovery] sync_dev refused: upstream touches protected paths" in text


def test_bridge_prompts_keep_external_sources_as_metadata_only() -> None:
    codex = _text(PROMPTS_DIR / "codex_track_attempt.txt")
    oracle = _text(PROMPTS_DIR / "oracle_initial.txt")
    assert "non-authoritative" in codex
    assert "Do NOT read Automath source" in codex
    assert "The admissible evidence" in codex
    assert "not as paper evidence" not in codex
    assert "不是 BEDC 论文证据" in oracle
    assert "不得读取或依赖 Automath source path" in oracle
    assert "本轮可用证据只限 BEDC" in oracle


def test_dev_sync_protects_clean_merge_boundaries() -> None:
    text = _text(SCRIPT_DIR / "dev_sync_resolver.py")
    assert "OURS_ON_CLEAN_MERGE_PATTERNS" in text
    assert "_settle_clean_merge_boundaries(before_head)" in text
    assert '"rm", "--cached", "--ignore-unmatch", path' in text
    assert '"checkout", before_ref, "--", path' in text
    assert "post-merge boundaries settled" in text


def test_candidate_inbox_holds_refinable_candidates() -> None:
    text = _text(SCRIPT_DIR / "candidate_inbox.py")
    assert "held: list[dict[str, Any]]" in text
    assert "REFINABLE_REASON_RE" in text
    assert "pre_gate_hold" in text
    assert "held_for_refinement" in text


def test_research_lane_recovers_held_candidates() -> None:
    text = _text(SCRIPT_DIR / "research_candidate_lane.py")
    assert '"pre_gate_hold"' in text
    assert '"held_for_refinement"' in text


def test_supervisor_runs_plain_review_research_lane() -> None:
    text = _text(SUPERVISOR)
    assert "PLAIN_MATH_REVIEW" in text
    assert "RESEARCH_CANDIDATE_LANE" in text
    assert "DEFAULT_RESEARCH_LANE_COOLDOWN_HOURS = 1.0" in text
    assert "DEFAULT_ORACLE_REFILL_RESEARCH_GRACE_MINUTES" in text
    assert "def trigger_research_lane_refinement()" in text
    assert "def candidate_inbox_has_refinement_backlog" in text
    assert "plain_math_review + research_candidate_lane" in text
    assert "--research-lane-cooldown-hours" in text
    assert "--oracle-refill-research-grace-minutes" in text
    assert "research_lane_refinement" in text
    assert "deferred oracle_board_refill" in text
    assert "does not write paper text directly" in text


def test_board_spawn_has_deterministic_judge_fallback() -> None:
    text = _text(SCRIPT_DIR / "board_spawn.py")
    assert "DETERMINISTIC_FALLBACK_SOURCES" in text
    assert "ANTI_PARAMETER_ECHO_RE" in text
    assert "def _deterministic_fallback_judge" in text
    assert "board_judge_unavailable" in text
    assert "Deterministic BOARD fallback admitted" in text


def test_research_lane_retries_soft_candidate_failures() -> None:
    text = _text(SCRIPT_DIR / "research_candidate_lane.py")
    assert "INBOX_SOFT_REJECT_SOURCES" in text
    assert "SOFT_RECOVERABLE_REASON_RE" in text
    assert "def _soft_recoverable_reject" in text
    assert "soft rejected inputs are re-read as" in text
    assert "plain BEDC-native obligations" in text
    assert "SOURCE_MARKER_RE" in text
    assert "source_marker_in_claim" in text


def test_structural_relation_miner_does_not_embed_source_excerpts() -> None:
    text = _text(SCRIPT_DIR / "structural_relation_miner.py")
    assert "must re-read those rows rather than trust a copied source excerpt" in text
    assert "Local evidence: {snippet}" not in text
    assert "_snippet_for" not in text


if __name__ == "__main__":
    test_supervisor_does_not_clear_stop_file()
    test_supervisor_runs_gated_dev_sync_resolver()
    test_supervisor_keeps_discovery_children_single_sync_entrypoint()
    test_supervisor_defaults_to_continuous_auto_dev_sync()
    test_supervisor_defaults_to_paper_native_discovery()
    test_supervisor_has_hard_branch_guard()
    test_supervisor_refill_can_recover_from_stale_circuit_breaker()
    test_supervisor_keeps_board_state_files_local_only()
    test_auto_discovery_dev_sync_is_opt_in_and_path_guarded()
    test_bridge_prompts_keep_external_sources_as_metadata_only()
    test_dev_sync_protects_clean_merge_boundaries()
    test_candidate_inbox_holds_refinable_candidates()
    test_research_lane_recovers_held_candidates()
    test_supervisor_runs_plain_review_research_lane()
    test_board_spawn_has_deterministic_judge_fallback()
    test_research_lane_retries_soft_candidate_failures()
    test_structural_relation_miner_does_not_embed_source_excerpts()
    print("test_git_sync_boundaries: ok")

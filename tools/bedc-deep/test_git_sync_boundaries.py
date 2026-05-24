#!/usr/bin/env python3
"""Static regression checks for BEDC paper-native Git sync boundaries."""

from pathlib import Path
import importlib.util


SCRIPT_DIR = Path(__file__).resolve().parent
SUPERVISOR = SCRIPT_DIR / "supervisor.py"
AUTO_DISCOVERY = SCRIPT_DIR / "auto_discovery.py"
PROMPTS_DIR = SCRIPT_DIR / "prompts"
CODEX_TRACK = SCRIPT_DIR / "codex_track.py"
PAPER_GAP_SCANNER = SCRIPT_DIR / "paper_gap_scanner.py"


def _load_supervisor_module():
    spec = importlib.util.spec_from_file_location("bedc_deep_supervisor_test", SUPERVISOR)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_supervisor_does_not_clear_stop_file() -> None:
    text = _text(SUPERVISOR)
    assert "STOP_FILE present; supervisor not starting" in text
    assert "STOP_FILE.unlink()" not in text


def test_supervisor_runs_gated_dev_sync_resolver() -> None:
    text = _text(SUPERVISOR)
    start = text.index("def git_sync_dev(")
    end = text.index("\ndef trigger_probe", start)
    body = text[start:end]
    assert "origin/auto-dev" in body or "dev_sync_resolver" in body
    assert "DEV_SYNC_RESOLVER" in body
    assert "subprocess.Popen" in body
    assert "communicate(timeout=timeout_seconds)" in body
    assert "deferred to next supervisor tick" in body
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


def test_supervisor_dev_sync_is_enabled_for_shared_integration() -> None:
    text = _text(SUPERVISOR)
    assert "DEFAULT_DEV_SYNC_COOLDOWN_MINUTES = 15" in text
    assert "DEFAULT_DEV_SYNC_ENABLED = True" in text
    assert "dev_sync_enabled = bool(args.dev_sync) and not bool(args.no_dev_sync)" in text
    assert "no_dev_sync = not dev_sync_enabled" in text
    assert "git_sync_dev(" in text
    assert "STARTUP_DEV_SYNC_TIMEOUT_SECONDS" in text
    assert "--no-dev-sync" in text
    assert "Default on so the BEDC branch stays joined to the shared integration trunk" in text
    assert "--status-once" in text


def test_supervisor_defaults_to_paper_native_discovery() -> None:
    text = _text(SUPERVISOR)
    assert "DEFAULT_ALLOW_LEAN_ADJACENT_DISCOVERY = False" in text
    assert "--allow-lean-adjacent-discovery" in text
    assert "paper-native supervisor defaults forbid" in text
    assert "Lean-adjacent discovery" in text
    assert "paper_review, research_lane" in text
    assert "bridge/local intake remain enabled" in text


def test_supervisor_oracle_candidate_generation_is_opt_in() -> None:
    text = _text(SUPERVISOR)
    assert "DEFAULT_ALLOW_ORACLE_CANDIDATE_GENERATION = False" in text
    assert "--allow-oracle-candidate-generation" in text
    assert '"allow_oracle_candidate_generation": args.allow_oracle_candidate_generation' in text
    assert "oracle_candidate_generation={'on' if args.allow_oracle_candidate_generation else 'off'}" in text
    assert "skipped oracle_board_refill" in text
    assert "oracle candidate generation is disabled by default" in text
    assert "Codex, bridge, and deterministic local lanes remain primary" in text
    assert "trigger_oracle_board_refill()" in text
    assert "oracle workers still drain explicit escalation tasks" in text


def test_codex_track_has_substance_guard_before_redline() -> None:
    text = _text(CODEX_TRACK)
    assert "PARAMETER_ECHO_RE" in text
    assert "def _substance_rejection" in text
    start = text.index("if codex_verdict == \"close\":")
    end = text.index("redline_t0 = time.time()", start)
    body = text[start:end]
    assert "_substance_rejection(target, parsed)" in body
    assert "substance_reject" in body


def test_paper_gap_scanner_does_not_emit_row_projection_targets() -> None:
    text = _text(PAPER_GAP_SCANNER)
    start = text.index("def _namecert_surface_candidates")
    end = text.index("\ndef _paper_label_set", start)
    body = text[start:end]
    assert "return []" in body
    assert "local obligation row projection" not in body


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
    assert "project_active_poll_agents" in body
    assert "--ignore-refill-circuit-breaker" in body
    assert "--allow-queue-without-tabs" in body
    assert "ignoring stale refill circuit breaker" in body
    assert "allowing queued refill" in body


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


def test_dev_sync_conflict_resolution_uses_codex_not_claude() -> None:
    text = _text(SCRIPT_DIR / "dev_sync_resolver.py")
    assert "import codex_orchestrator" in text
    assert "codex_orchestrator.codex_exec" in text
    assert "Codex-driven conflict resolution" in text
    assert "CLAUDE_PATH" not in text
    assert "_claude_exec" not in text


def test_candidate_inbox_holds_refinable_candidates() -> None:
    text = _text(SCRIPT_DIR / "candidate_inbox.py")
    assert "held: list[dict[str, Any]]" in text
    assert "REFINABLE_REASON_RE" in text
    assert "pre_gate_hold" in text
    assert "held_for_refinement" in text
    assert "r\"too_weak|below_fit_threshold|below_novelty_threshold|" in text
    assert "predicted_line_cap_overflow|logic_packet_gate" not in text
    rejection_start = text.index("def _rejection_reason")
    rejection_end = text.index("\ndef screen_candidates", rejection_start)
    rejection_body = text[rejection_start:rejection_end]
    assert "below_fit_threshold" not in rejection_body
    assert "below_novelty_threshold" not in rejection_body


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
    assert "local lanes must drain/refine it before oracle refill" in text
    assert "should_defer_oracle_refill_for_research" in text
    assert "candidate refinement grace elapsed" in text
    assert "does not write paper text directly" in text


def test_loning_pipeline_signals_do_not_inject_prompt_advice() -> None:
    assimilator = _text(SCRIPT_DIR / "loning_assimilator.py")
    board_spawn = _text(SCRIPT_DIR / "board_spawn.py")
    auto_discovery = _text(SCRIPT_DIR / "auto_discovery.py")
    oracle_refill = _text(SCRIPT_DIR / "oracle_board_refill.py")
    supervisor = _text(SUPERVISOR)
    dashboard = _text(SCRIPT_DIR / "dashboard.py")

    assert "VERSION = \"loning-pipeline-signals\"" in assimilator
    assert "signal_counts" in assimilator
    assert "latest_signal_summary" in assimilator
    assert "latest_prompt_block" not in assimilator
    assert "Loning assimilation advice" not in assimilator
    assert "prompt_block" not in assimilator
    assert "build_advice" not in assimilator

    for text in (board_spawn, auto_discovery, oracle_refill):
        assert "latest_prompt_block" not in text
        assert "Loning assimilation advice" not in text

    assert "structured local pipeline signals" in supervisor
    assert "signal_counts" in supervisor
    assert "advice_count" not in supervisor
    assert "legacy advice fields ignored" in dashboard


def test_oracle_refill_defer_uses_material_backlog_and_grace() -> None:
    supervisor = _load_supervisor_module()
    material_health = {
        "by_event": {"held_for_refinement": 1},
        "refinement_reasons": [{"reason": "missing_local_inputs", "count": 1}],
    }
    non_material_health = {
        "by_event": {"held_for_refinement": 1},
        "refinement_reasons": [
            {
                "reason": (
                    "predicted_line_cap_overflow:"
                    "papers/bedc/parts/concrete_instances/example.tex:833"
                ),
                "count": 1,
            }
        ],
    }

    assert supervisor.candidate_inbox_has_refinement_backlog(material_health)
    assert not supervisor.candidate_inbox_has_refinement_backlog(non_material_health)

    assert supervisor.should_defer_oracle_refill_for_research(
        research_lane_triggered=False,
        inbox_health=material_health,
        since_research_lane_m=5.0,
        grace_minutes=20.0,
    ) == (True, "material_refinement_backlog_within_grace")
    assert supervisor.should_defer_oracle_refill_for_research(
        research_lane_triggered=False,
        inbox_health=material_health,
        since_research_lane_m=25.0,
        grace_minutes=20.0,
    ) == (False, "material_refinement_backlog_grace_elapsed")
    assert supervisor.should_defer_oracle_refill_for_research(
        research_lane_triggered=False,
        inbox_health=non_material_health,
        since_research_lane_m=5.0,
        grace_minutes=20.0,
    ) == (False, "no_material_refinement_backlog")


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
    assert '"warnings": score_warnings' in text


def test_discovery_cross_check_failure_does_not_append_candidates() -> None:
    text = _text(SCRIPT_DIR / "auto_discovery.py")
    assert "holding phase-1 candidates outside BOARD" in text
    assert "kept = []" in text
    assert "codex_cross_check_unavailable:" in text
    assert "falling back to phase-1 candidates without cross-check" not in text


def test_structural_relation_miner_does_not_embed_source_excerpts() -> None:
    text = _text(SCRIPT_DIR / "structural_relation_miner.py")
    assert "must re-read those rows rather than trust a copied source excerpt" in text
    assert "Local evidence: {snippet}" not in text
    assert "_snippet_for" not in text


if __name__ == "__main__":
    test_supervisor_does_not_clear_stop_file()
    test_supervisor_runs_gated_dev_sync_resolver()
    test_supervisor_keeps_discovery_children_single_sync_entrypoint()
    test_supervisor_dev_sync_is_enabled_for_shared_integration()
    test_supervisor_defaults_to_paper_native_discovery()
    test_supervisor_oracle_candidate_generation_is_opt_in()
    test_codex_track_has_substance_guard_before_redline()
    test_paper_gap_scanner_does_not_emit_row_projection_targets()
    test_supervisor_has_hard_branch_guard()
    test_supervisor_refill_can_recover_from_stale_circuit_breaker()
    test_supervisor_keeps_board_state_files_local_only()
    test_auto_discovery_dev_sync_is_opt_in_and_path_guarded()
    test_bridge_prompts_keep_external_sources_as_metadata_only()
    test_dev_sync_protects_clean_merge_boundaries()
    test_dev_sync_conflict_resolution_uses_codex_not_claude()
    test_candidate_inbox_holds_refinable_candidates()
    test_research_lane_recovers_held_candidates()
    test_supervisor_runs_plain_review_research_lane()
    test_oracle_refill_defer_uses_material_backlog_and_grace()
    test_board_spawn_has_deterministic_judge_fallback()
    test_research_lane_retries_soft_candidate_failures()
    test_discovery_cross_check_failure_does_not_append_candidates()
    test_structural_relation_miner_does_not_embed_source_excerpts()
    print("test_git_sync_boundaries: ok")

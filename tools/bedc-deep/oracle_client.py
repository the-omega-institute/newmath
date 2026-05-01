#!/usr/bin/env python3
"""BEDC oracle client — codex-orchestrated deep reasoning + LaTeX writeback.

Flow per target:
  Stage 1   Oracle deep-reasoning loop (no static max_turns):
              - codex orchestrator decides progress_delta + next_prompt per turn
              - verdict comes from oracle response regex (BREAKTHROUGH / Q.E.D. / STUCK)
                or safety nets (3 consecutive low progress_delta, wall-clock 12h)
              - per-turn checkpoint to state/<target>/cursor.json so a crash
                resumes from the next turn instead of restarting at 0
              - terminal turn issues WRITE_PAPER_LATEX prompt → raw LaTeX output
  Stage 1.5 Topic discovery: codex extracts adjacent claim candidates from the
              full transcript, dedup against BOARD.md, append accepted entries
              as new B-XX rows for the next loop pass.
  Stage 2   Killo-golden writeback: independent claude -p reads transcript and
              raw LaTeX, applies hygiene checklist, appends accepted block to
              papers/bedc/parts/<theme>/<concept>.tex, runs `make` to verify.

Hard rule: this lane never edits lean4/. Stage 2 only edits papers/bedc/parts/.
"""

from __future__ import annotations

import argparse
import json
import re
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone
from pathlib import Path

from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
import os

from dispatch_bedc_target import SCRIPT_DIR, BedcTarget, build_initial_prompt, parse_board, BOARD_PATH
import codex_orchestrator
import killo_golden_writeback
from locks import file_lock


ORACLE_SERVER = "http://localhost:8767"
STATE_DIR = SCRIPT_DIR / "state"
TARGETS_DIR = SCRIPT_DIR / "targets"
WRITE_LATEX_PROMPT_PATH = SCRIPT_DIR / "prompts" / "write_paper_latex.txt"
DEFAULT_SAFETY_NET_TURNS = 3
DEFAULT_WALL_CLOCK_HOURS = 12
DEFAULT_LOW_PROGRESS_THRESHOLD = 1


def http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def http_get(url: str, timeout: int = 10) -> dict:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def server_status(server_url: str) -> dict:
    return http_get(f"{server_url}/status", timeout=5)


def status_line(status: dict) -> str:
    recent = status.get("active_recent_agents") or []
    return (
        f"diagnosis={status.get('diagnosis', 'unknown')} "
        f"queue={status.get('queue_length', '?')} "
        f"busy={status.get('agents_busy', '?')}/{status.get('max_agents', '?')} "
        f"recent_agents={len(recent)} completed={status.get('completed', '?')}"
    )


def print_status_hint(server_url: str) -> dict:
    try:
        status = server_status(server_url)
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise SystemExit(
            f"oracle server is not reachable at {server_url}; "
            "start: python3 tools/bedc-deep/bedc_oracle_server.py"
        ) from exc
    print(f"[status] {status_line(status)}", flush=True)
    if status.get("diagnosis") == "queue_waiting_for_browser_agent":
        print("[status] queued work has no active BEDC ChatGPT tab.", flush=True)
        print("[status] install userscript: tools/bedc-deep/bedc_oracle_macos.user.js", flush=True)
        print("[status] open: https://chatgpt.com/?bedc=1 and click Start in the BEDC panel", flush=True)
    return status


def cancel_tasks(server_url: str, *, task_id: str = "", all_tasks: bool = False) -> dict:
    payload = {"all": True} if all_tasks else {"task_id": task_id}
    return http_post(f"{server_url}/cancel", payload, timeout=30)


def watch_status(server_url: str, interval: int) -> None:
    while True:
        status = print_status_hint(server_url)
        queued = status.get("queued_tasks") or []
        if queued:
            oldest = queued[0]
            print(
                "[watch] oldest="
                f"{oldest.get('task_id', '')} age={oldest.get('age_seconds', '?')}s "
                f"chars={oldest.get('prompt_chars', '?')}",
                flush=True,
            )
        time.sleep(max(1, interval))


def submit_turn(
    server_url: str,
    task_id: str,
    prompt: str,
    conversation_id: str = "",
    model: str = "chatgpt-5.5-pro",
) -> dict:
    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
        "tag": "bedc-deep",
    }
    if conversation_id:
        payload["conversation_id"] = conversation_id
    endpoint = "/continue" if conversation_id else "/submit"
    return http_post(f"{server_url}{endpoint}", payload, timeout=30)


def wait_for_recent_agent(server_url: str, seconds: int, poll_interval: int) -> bool:
    if seconds <= 0:
        return True
    deadline = time.time() + seconds
    while time.time() < deadline:
        status = print_status_hint(server_url)
        if status.get("active_recent_agents"):
            return True
        time.sleep(max(1, poll_interval))
    return False


def poll_result(
    server_url: str,
    task_id: str,
    timeout: int,
    poll_interval: int,
    status_interval: int,
) -> str:
    start = time.time()
    next_status_at = start
    while time.time() - start < timeout:
        try:
            data = http_get(f"{server_url}/result/{task_id}", timeout=10)
            if data.get("status") == "completed":
                return data.get("response", "")
        except Exception:
            pass
        now = time.time()
        if now >= next_status_at:
            try:
                status = server_status(server_url)
                print(f"[wait:{task_id}] {status_line(status)}", flush=True)
                if status.get("diagnosis") == "queue_waiting_for_browser_agent":
                    print("[wait] no active BEDC ChatGPT tab is polling; start one with https://chatgpt.com/?bedc=1", flush=True)
            except Exception as exc:
                print(f"[wait:{task_id}] status unavailable: {exc}", flush=True)
            next_status_at = now + max(1, status_interval)
        time.sleep(poll_interval)
    return ""


def artifact_dir(target: BedcTarget) -> Path:
    path = TARGETS_DIR / target.slug
    path.mkdir(parents=True, exist_ok=True)
    return path


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


# ---------------------------------------------------------------------------
# Verdict detection (response-side regex)
# ---------------------------------------------------------------------------

DONE_RE = re.compile(r"\b(BREAKTHROUGH|PROVED|Q\.E\.D\.?|QED)\b", re.IGNORECASE)
STUCK_RE = re.compile(r"\bSTUCK\b", re.IGNORECASE)
ERROR_RE = re.compile(r"^\s*ERROR\b", re.IGNORECASE)


def detect_response_verdict(text: str) -> str:
    if ERROR_RE.match(text or ""):
        return "agent_error"
    if STUCK_RE.search(text or ""):
        return "stuck"
    if DONE_RE.search(text or ""):
        return "done"
    return "open"


# ---------------------------------------------------------------------------
# Per-turn checkpoint (resumability)
# ---------------------------------------------------------------------------


def cursor_path(target: BedcTarget) -> Path:
    return STATE_DIR / target.slug / "cursor.json"


def load_cursor(target: BedcTarget) -> dict:
    path = cursor_path(target)
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def save_cursor(target: BedcTarget, cursor: dict) -> None:
    path = cursor_path(target)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(cursor, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# BOARD.md append (Stage 1.5 fan-out)
# ---------------------------------------------------------------------------


DEFAULT_CANDIDATE_FIT_THRESHOLD = 7
DEFAULT_CANDIDATE_NOVELTY_THRESHOLD = 6


def existing_target_ids() -> list[str]:
    text = BOARD_PATH.read_text(encoding="utf-8")
    return re.findall(r"^### (B-\d+)\b", text, flags=re.MULTILINE)


def next_target_id() -> str:
    ids = existing_target_ids()
    nums = [int(i.split("-")[1]) for i in ids if i.startswith("B-")]
    next_num = (max(nums) + 1) if nums else 1
    return f"B-{next_num:02d}"


def render_candidate_entry(target_id: str, candidate: dict) -> str:
    title = candidate.get("title", "(untitled)")
    claim = candidate.get("concrete_claim", "")
    inputs = candidate.get("local_inputs") or []
    rationale = candidate.get("rationale", "")
    fit = candidate.get("fit_score", "?")
    novelty = candidate.get("novelty", "?")
    inputs_block = "\n".join(f"- `{p}`" for p in inputs) if inputs else "- (none provided)"
    return (
        f"\n### {target_id} - {title}\n\n"
        f"| field | value |\n"
        f"|---|---|\n"
        f"| Status | Candidate (auto-spawned) |\n"
        f"| Source | bedc-deep topic discovery |\n"
        f"| Object | {title} |\n"
        f"| Layer | adjacent |\n"
        f"| Route | proof |\n"
        f"| Risk | unknown |\n"
        f"| Fit | {fit}/10 |\n"
        f"| Novelty | {novelty}/10 |\n\n"
        f"Problem:\n{claim}\n\n"
        f"Local inputs:\n{inputs_block}\n\n"
        f"Rationale:\n{rationale}\n\n---\n"
    )


def append_candidates_to_board(
    candidates: list[dict],
    *,
    fit_threshold: int = DEFAULT_CANDIDATE_FIT_THRESHOLD,
    novelty_threshold: int = DEFAULT_CANDIDATE_NOVELTY_THRESHOLD,
) -> list[str]:
    accepted: list[str] = []
    if not candidates:
        return accepted
    with file_lock("board"):
        existing_titles = set()
        for line in BOARD_PATH.read_text(encoding="utf-8").splitlines():
            m = re.match(r"^### B-\d+\s+-\s+(.+)$", line)
            if m:
                existing_titles.add(m.group(1).strip().lower())
        appended_blocks: list[str] = []
        for cand in candidates:
            try:
                fit = int(cand.get("fit_score", 0))
                nov = int(cand.get("novelty", 0))
            except (TypeError, ValueError):
                continue
            if fit < fit_threshold or nov < novelty_threshold:
                continue
            title = cand.get("title", "").strip()
            if not title or title.lower() in existing_titles:
                continue
            new_id = next_target_id_with_local(existing_titles, accepted)
            appended_blocks.append(render_candidate_entry(new_id, cand))
            existing_titles.add(title.lower())
            accepted.append(new_id)
        if appended_blocks:
            original = BOARD_PATH.read_text(encoding="utf-8").rstrip()
            BOARD_PATH.write_text(original + "\n" + "\n".join(appended_blocks) + "\n", encoding="utf-8")
    return accepted


def next_target_id_with_local(existing_titles: set, already_accepted: list[str]) -> str:
    """Compute next B-XX id including in-flight accepted ids from this batch."""
    text = BOARD_PATH.read_text(encoding="utf-8")
    ids = re.findall(r"^### (B-\d+)\b", text, flags=re.MULTILINE)
    ids.extend(already_accepted)
    nums = [int(i.split("-")[1]) for i in ids if i.startswith("B-")]
    next_num = (max(nums) + 1) if nums else 1
    return f"B-{next_num:02d}"


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _build_full_transcript(out_dir: Path, turns: list[dict]) -> str:
    parts: list[str] = []
    for t in turns:
        n = t.get("turn", "?")
        prompt_file = out_dir / f"turn_{n:02d}_prompt.md" if isinstance(n, int) else None
        response_file = out_dir / f"turn_{n:02d}_response.md" if isinstance(n, int) else None
        prompt_text = prompt_file.read_text(encoding="utf-8") if prompt_file and prompt_file.exists() else "(missing)"
        response_text = response_file.read_text(encoding="utf-8") if response_file and response_file.exists() else "(missing)"
        parts.append(f"=== Turn {n} ===\nPROMPT:\n{prompt_text}\n\nRESPONSE:\n{response_text}\n")
    return "\n".join(parts)


def run_target(args: argparse.Namespace, target: BedcTarget) -> dict:
    """Run Stage 1 → 1.5 → 2 for one target. Returns final state dict."""
    out_dir = artifact_dir(target)

    # Pre-flight: if the target's Object is already covered by a paper marker
    # or a theorem/lemma/proposition label, skip Stage 1 entirely. The oracle
    # would otherwise burn hours re-deriving an existing result and Stage 2
    # would reject the duplicate. Override with --force.
    if not getattr(args, "force", False):
        from prior_art import find_paper_coverage
        coverage = find_paper_coverage(target.fields.get("Object", ""))
        if coverage:
            print(
                f"[stage1] target {target.target_id} already covered by paper "
                f"({len(coverage)} hits); skipping (use --force to override)",
                flush=True,
            )
            for h in coverage[:3]:
                print(f"  - {h['kind']}: {h['matched']} @ {h['file']}:{h['line']}", flush=True)
            state = {
                "target_id": target.target_id,
                "title": target.title,
                "started_at": _now_iso(),
                "completed_at": _now_iso(),
                "stage1_verdict": "already_in_paper",
                "paper_coverage": coverage[:20],
            }
            write_text(STATE_DIR / f"{target.slug}.json", json.dumps(state, ensure_ascii=False, indent=2))
            return state

    cursor = load_cursor(target)
    turns: list[dict] = cursor.get("turns") or []
    conversation_id = cursor.get("conversation_id") or ""
    started_at = cursor.get("started_at") or _now_iso()
    progress_history: list[int] = [t.get("progress_delta", 0) for t in turns]
    wall_clock_start = time.time()

    print_status_hint(args.server)
    if args.preflight_agent_wait > 0 and not wait_for_recent_agent(
        args.server, args.preflight_agent_wait, args.poll_interval
    ):
        raise SystemExit(
            "no active BEDC ChatGPT tab appeared before preflight timeout; "
            "open https://chatgpt.com/?bedc=1 and click Start"
        )

    # ----- Stage 1: deep reasoning loop -----
    if not turns:
        prompt = build_initial_prompt(target)
    else:
        prompt = cursor.get("pending_prompt") or build_initial_prompt(target)

    verdict = "open"
    while True:
        turn_idx = len(turns)
        wall_hours = (time.time() - wall_clock_start) / 3600.0
        if wall_hours >= args.wall_clock_hours:
            print(f"[stage1] wall-clock ceiling {args.wall_clock_hours}h reached; stopping", flush=True)
            verdict = "stuck"
            break

        task_id = f"bedc_{target.target_id.lower()}_t{turn_idx}_{int(time.time() * 1000)}"
        write_text(out_dir / f"turn_{turn_idx:02d}_prompt.md", prompt)
        submit = submit_turn(args.server, task_id, prompt, conversation_id, model=args.model)
        if "error" in submit:
            raise SystemExit(f"oracle submit failed: {submit['error']}")
        conversation_id = submit.get("conversation_id") or conversation_id
        print(
            f"[stage1] task={task_id} conv={conversation_id[:12]} turn={turn_idx} "
            f"queue_position={submit.get('queue_position', '?')}",
            flush=True,
        )
        response = poll_result(
            args.server,
            task_id,
            args.timeout,
            args.poll_interval,
            args.status_interval,
        )
        if not response:
            turns.append({"turn": turn_idx, "task_id": task_id, "verdict": "timeout"})
            verdict = "stuck"
            save_cursor(target, {
                "turns": turns,
                "conversation_id": conversation_id,
                "started_at": started_at,
            })
            break

        duplicate_of = None
        for prev_idx in range(turn_idx):
            prev_response_path = out_dir / f"turn_{prev_idx:02d}_response.md"
            if prev_response_path.exists() and prev_response_path.read_text(encoding="utf-8") == response:
                duplicate_of = prev_idx
                break
        if duplicate_of is not None:
            duplicate_path = out_dir / f"turn_{turn_idx:02d}_response.duplicate.md"
            write_text(duplicate_path, response)
            raise RuntimeError(
                f"oracle returned exact duplicate response for turn {turn_idx} "
                f"(matches turn {duplicate_of}); wrote {duplicate_path}"
            )

        write_text(out_dir / f"turn_{turn_idx:02d}_response.md", response)

        response_verdict = detect_response_verdict(response)
        if response_verdict == "agent_error":
            turns.append({"turn": turn_idx, "task_id": task_id, "verdict": "agent_error"})
            verdict = "stuck"
            save_cursor(target, {
                "turns": turns,
                "conversation_id": conversation_id,
                "started_at": started_at,
            })
            break

        # codex orchestrator: progress + next prompt
        target_context = (out_dir / f"turn_00_prompt.md").read_text(encoding="utf-8") if (out_dir / "turn_00_prompt.md").exists() else ""
        codex_result = codex_orchestrator.orchestrate_turn(
            target_id=target.target_id,
            target_title=target.title,
            target_context=target_context[:8000],
            history_turns=turns,
            last_response=response,
            target_tex_file=None,
        )
        if codex_result.ok and codex_result.parsed:
            progress_delta = int(codex_result.parsed.get("progress_delta", 0) or 0)
            contribution = str(codex_result.parsed.get("contribution_one_liner", ""))
            next_prompt = str(codex_result.parsed.get("next_prompt", "")) or _fallback_next_prompt(turn_idx)
        else:
            print(f"[stage1] codex orchestrator failed: {codex_result.error or 'no parsed JSON'}; using fallback prompt", flush=True)
            progress_delta = 0
            contribution = "(codex orchestrator unavailable)"
            next_prompt = _fallback_next_prompt(turn_idx)

        turns.append({
            "turn": turn_idx,
            "task_id": task_id,
            "progress_delta": progress_delta,
            "contribution_one_liner": contribution,
            "response_verdict": response_verdict,
        })
        progress_history.append(progress_delta)
        save_cursor(target, {
            "turns": turns,
            "conversation_id": conversation_id,
            "started_at": started_at,
            "pending_prompt": next_prompt,
        })

        if response_verdict == "done":
            verdict = "done"
            break
        if response_verdict == "stuck":
            verdict = "stuck"
            break
        # safety net: N consecutive low-progress turns → stuck
        recent = progress_history[-args.safety_net_turns:]
        if (
            len(recent) >= args.safety_net_turns
            and all(p <= args.low_progress_threshold for p in recent)
        ):
            print(
                f"[stage1] safety-net: {args.safety_net_turns} consecutive turns "
                f"with progress_delta ≤ {args.low_progress_threshold}; stopping",
                flush=True,
            )
            verdict = "stuck"
            break

        prompt = next_prompt

    # ----- Stage 1 terminal: WRITE_PAPER_LATEX (only if done) -----
    raw_latex_path = out_dir / "raw_oracle_latex.md"
    if verdict == "done":
        latex_prompt = WRITE_LATEX_PROMPT_PATH.read_text(encoding="utf-8").format(
            target_id=target.target_id,
            target_title=target.title,
        )
        task_id = f"bedc_{target.target_id.lower()}_writelatex_{int(time.time() * 1000)}"
        write_text(out_dir / "turn_writelatex_prompt.md", latex_prompt)
        submit = submit_turn(args.server, task_id, latex_prompt, conversation_id, model=args.model)
        if "error" not in submit:
            print(f"[stage1] terminal WRITE_PAPER_LATEX submitted: {task_id}", flush=True)
            latex_response = poll_result(
                args.server,
                task_id,
                args.timeout,
                args.poll_interval,
                args.status_interval,
            )
            if latex_response:
                write_text(raw_latex_path, latex_response)
            else:
                print("[stage1] WRITE_PAPER_LATEX returned empty; demoting to stuck", flush=True)
                verdict = "stuck"
        else:
            print(f"[stage1] terminal submit failed: {submit['error']}", flush=True)
            verdict = "stuck"

    # ----- Stage 1.5: topic discovery (only if done) -----
    spawned_ids: list[str] = []
    if verdict == "done":
        full_transcript = _build_full_transcript(out_dir, turns)
        write_text(out_dir / "full_transcript.md", full_transcript)
        board_content = BOARD_PATH.read_text(encoding="utf-8")
        td = codex_orchestrator.discover_topics(
            target_id=target.target_id,
            target_title=target.title,
            full_transcript=full_transcript[:60000],
            board_content=board_content[:30000],
        )
        if td.ok and td.parsed:
            candidates = td.parsed.get("candidates") or []
            write_text(out_dir / "candidates.json", json.dumps(td.parsed, ensure_ascii=False, indent=2))
            spawned_ids = append_candidates_to_board(
                candidates,
                fit_threshold=args.candidate_fit_threshold,
                novelty_threshold=args.candidate_novelty_threshold,
            )
            print(f"[stage1.5] candidates surfaced={len(candidates)} accepted={len(spawned_ids)}", flush=True)
        else:
            print(f"[stage1.5] discovery skipped: {td.error or 'no parsed JSON'}", flush=True)

    # ----- Stage 2: killo-golden writeback (only if done + raw latex present) -----
    stage2_summary: dict = {}
    if verdict == "done" and raw_latex_path.exists():
        suggested = _extract_insertion_target(raw_latex_path.read_text(encoding="utf-8"))
        result = killo_golden_writeback.writeback(
            target_id=target.target_id,
            target_title=target.title,
            transcript_dir=out_dir,
            raw_latex_path=raw_latex_path,
            suggested_target_tex=suggested,
        )
        stage2_summary = {
            "ok": result.ok,
            "verdict": result.verdict,
            "tex_file": result.tex_file,
            "appended": result.appended,
            "compile_ok": result.compile_ok,
            "rejection_reasons": result.rejection_reasons,
            "error": result.error,
        }
        write_text(out_dir / "stage2_result.json", json.dumps(stage2_summary, ensure_ascii=False, indent=2))
        if result.appended and result.compile_ok:
            print(f"[stage2] appended to {result.tex_file} and `make` succeeded", flush=True)
        else:
            print(f"[stage2] verdict={result.verdict} appended={result.appended} compile_ok={result.compile_ok}", flush=True)

    final_state = {
        "target_id": target.target_id,
        "title": target.title,
        "started_at": started_at,
        "completed_at": _now_iso(),
        "conversation_id": conversation_id,
        "turns": turns,
        "stage1_verdict": verdict,
        "stage15_spawned": spawned_ids,
        "stage2": stage2_summary,
    }
    write_text(STATE_DIR / f"{target.slug}.json", json.dumps(final_state, ensure_ascii=False, indent=2))
    return final_state


def _extract_insertion_target(latex_response: str) -> str:
    m = re.search(r"Insertion target:\s*(papers/bedc/parts/[^\s`]+\.tex)", latex_response or "")
    if m:
        return m.group(1)
    return ""


def _fallback_next_prompt(turn_idx: int) -> str:
    fallbacks = [
        "Take the most concrete sub-claim you've made and formalize it as a precise lemma with explicit hypotheses. Then attempt a complete proof.",
        "Find the weakest link in your last argument. Either close it with a proof or construct a small finite countermodel that breaks it.",
        "Separate the definitional part from the policy-assumption part of your last claim. Which sentence is doing the real work?",
        "If you reach a complete proof, conclude with Q.E.D. on a single canonical statement and list the minimal lemma sequence used.",
    ]
    return fallbacks[turn_idx % len(fallbacks)]


# ---------------------------------------------------------------------------
# Entry
# ---------------------------------------------------------------------------


def in_progress_marker(target: BedcTarget) -> Path:
    return STATE_DIR / target.slug / ".in_progress"


def claim_next_unfinished() -> BedcTarget | None:
    """Pick one unfinished+unclaimed target under target-picker lock."""
    with file_lock("target_picker"):
        targets = parse_board()
        for t in targets.values():
            done = (STATE_DIR / f"{t.slug}.json").exists()
            marker = in_progress_marker(t)
            if done or marker.exists():
                continue
            marker.parent.mkdir(parents=True, exist_ok=True)
            marker.write_text(f"pid={os.getpid()} ts={_now_iso()}\n", encoding="utf-8")
            return t
    return None


def release_claim(target: BedcTarget) -> None:
    marker = in_progress_marker(target)
    if marker.exists():
        try:
            marker.unlink()
        except OSError:
            pass


def _run_target_safe(args: argparse.Namespace, target: BedcTarget) -> dict:
    """Run a single target; always release its in-progress claim on exit."""
    try:
        return run_target(args, target)
    except KeyboardInterrupt:
        raise
    except Exception as exc:
        print(f"[loop] target {target.target_id} crashed: {exc}", flush=True)
        write_text(STATE_DIR / f"{target.slug}.json", json.dumps({
            "target_id": target.target_id,
            "title": target.title,
            "stage1_verdict": "crashed",
            "error": str(exc),
            "completed_at": _now_iso(),
        }, ensure_ascii=False, indent=2))
        return {"target_id": target.target_id, "stage1_verdict": "crashed"}
    finally:
        release_claim(target)


def run_loop(args: argparse.Namespace) -> int:
    targets = parse_board()
    if not args.target_id and not args.loop:
        print("error: either pass a target_id or --loop", flush=True)
        return 2

    if args.target_id:
        target = targets.get(args.target_id)
        if target is None:
            known = ", ".join(targets)
            raise SystemExit(f"unknown target {args.target_id}; known targets: {known}")
        marker = in_progress_marker(target)
        marker.parent.mkdir(parents=True, exist_ok=True)
        marker.write_text(f"pid={os.getpid()} ts={_now_iso()}\n", encoding="utf-8")
        try:
            run_target(args, target)
        finally:
            release_claim(target)
        return 0

    parallel = max(1, args.parallel)
    print(f"[loop] starting --loop with parallel={parallel}", flush=True)

    if parallel == 1:
        while True:
            target = claim_next_unfinished()
            if target is None:
                print("[loop] no unfinished targets remain; exiting", flush=True)
                return 0
            print(f"[loop] picking {target.target_id} ({target.title})", flush=True)
            try:
                _run_target_safe(args, target)
            except KeyboardInterrupt:
                print("[loop] interrupted by user", flush=True)
                release_claim(target)
                return 130

    with ThreadPoolExecutor(max_workers=parallel) as pool:
        futures = []
        for _ in range(parallel):
            t = claim_next_unfinished()
            if t is None:
                break
            print(f"[loop] dispatch {t.target_id} ({t.title})", flush=True)
            futures.append(pool.submit(_run_target_safe, args, t))
        try:
            while futures:
                done, pending = wait(futures, return_when=FIRST_COMPLETED)
                futures = list(pending)
                for _ in done:
                    nt = claim_next_unfinished()
                    if nt is None:
                        continue
                    print(f"[loop] dispatch {nt.target_id} ({nt.title})", flush=True)
                    futures.append(pool.submit(_run_target_safe, args, nt))
        except KeyboardInterrupt:
            print("[loop] interrupted by user; in-flight workers will continue until safe stop", flush=True)
            return 130
    print("[loop] all dispatched; pool drained; BOARD has no further unfinished targets", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run a BEDC target through the codex-orchestrated oracle bridge")
    parser.add_argument("target_id", nargs="?", help="Target id such as B-01")
    parser.add_argument("--loop", action="store_true", help="Process unfinished BOARD targets until BOARD is empty")
    parser.add_argument("--parallel", type=int, default=1, help="Number of concurrent target workers in --loop mode (default 1; cap to active ChatGPT tabs)")
    parser.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD, help="Minimum fit_score for Stage 1.5 to accept a spawned candidate")
    parser.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD, help="Minimum novelty for Stage 1.5 to accept a spawned candidate")
    parser.add_argument("--force", action="store_true", help="Bypass already-in-paper pre-flight check")
    parser.add_argument("--server", default=ORACLE_SERVER, help="Oracle server URL")
    parser.add_argument("--model", default="chatgpt-5.5-pro", help="Model name passed to the oracle server")
    parser.add_argument("--timeout", type=int, default=14400, help="Per-turn timeout in seconds")
    parser.add_argument("--poll-interval", type=int, default=30, help="Polling interval in seconds")
    parser.add_argument("--status-interval", type=int, default=30, help="Status print interval while waiting")
    parser.add_argument("--preflight-agent-wait", type=int, default=0, help="Wait this many seconds for an active browser agent before submitting")
    parser.add_argument("--safety-net-turns", type=int, default=DEFAULT_SAFETY_NET_TURNS, help="Stop if this many consecutive turns have low progress")
    parser.add_argument("--low-progress-threshold", type=int, default=DEFAULT_LOW_PROGRESS_THRESHOLD, help="Threshold for the safety net")
    parser.add_argument("--wall-clock-hours", type=float, default=DEFAULT_WALL_CLOCK_HOURS, help="Hard ceiling on Stage 1 wall-clock per target")
    parser.add_argument("--status", action="store_true", help="Print server status and exit")
    parser.add_argument("--watch-status", type=int, default=0, metavar="SECONDS", help="Continuously print server status every N seconds")
    parser.add_argument("--cancel-task", default="", help="Cancel one queued or pending task id")
    parser.add_argument("--cancel-all", action="store_true", help="Cancel all queued and pending tasks")
    args = parser.parse_args()

    if args.cancel_all or args.cancel_task:
        print(json.dumps(
            cancel_tasks(args.server, task_id=args.cancel_task, all_tasks=args.cancel_all),
            ensure_ascii=False,
            indent=2,
        ))
        return 0
    if args.watch_status > 0:
        try:
            watch_status(args.server, args.watch_status)
        except KeyboardInterrupt:
            print("\n[watch] stopped", flush=True)
        return 0
    if args.status:
        print(json.dumps(print_status_hint(args.server), ensure_ascii=False, indent=2))
        return 0
    return run_loop(args)


if __name__ == "__main__":
    raise SystemExit(main())

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
from typing import Optional

from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
import os

from dispatch_bedc_target import SCRIPT_DIR, BedcTarget, build_initial_prompt, parse_board, BOARD_PATH, build_context_block
import codex_orchestrator
import killo_golden_writeback
import lifecycle
import stage0_quickpath
import codex_track  # v2 codex track
import board_spawn  # v2 BOARD spawn gate
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
    pdf_base64: str = "",
    pdf_name: str = "",
) -> dict:
    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
        "tag": "bedc-deep",
    }
    if conversation_id:
        payload["conversation_id"] = conversation_id
    if pdf_base64:
        payload["pdf_base64"] = pdf_base64
        payload["pdf_name"] = pdf_name or "main.pdf"
    endpoint = "/continue" if conversation_id else "/submit"
    return http_post(f"{server_url}{endpoint}", payload, timeout=60)


# Cache encoded PDF — read once per inner process to avoid re-encoding 2 MB
# every initial turn. Re-reads only when file mtime changes.
_PDF_CACHE: dict = {"path": None, "mtime": None, "b64": None, "name": None}


def encode_pdf_for_attach(pdf_path: Optional[Path] = None) -> tuple[str, str]:
    """Return (base64, filename) ready for submit_turn. Empty strings if
    pdf_path is None or file missing. Caches across calls."""
    import base64
    if pdf_path is None or not Path(pdf_path).exists():
        return ("", "")
    p = Path(pdf_path)
    try:
        st = p.stat()
    except OSError:
        return ("", "")
    if (_PDF_CACHE["path"] == str(p) and _PDF_CACHE["mtime"] == st.st_mtime
            and _PDF_CACHE["b64"]):
        return (_PDF_CACHE["b64"], _PDF_CACHE["name"])
    try:
        b64 = base64.b64encode(p.read_bytes()).decode("ascii")
    except OSError:
        return ("", "")
    _PDF_CACHE.update({"path": str(p), "mtime": st.st_mtime, "b64": b64, "name": p.name})
    return (b64, p.name)


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
    """Atomic write: write to a sibling .tmp then os.replace, so concurrent
    readers / writers never see a half-written file. Eliminates the
    duplicate-content corruption observed on B-09 when supervisor's reset
    sweep raced with run_target's final state write."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


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
    write_text(path, json.dumps(cursor, ensure_ascii=False, indent=2) + "\n")


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
            write_text(BOARD_PATH, original + "\n" + "\n".join(appended_blocks) + "\n")
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
            lifecycle.annotate(state, attempts=int((load_cursor(target).get("attempts") or 1)))
            write_text(STATE_DIR / f"{target.slug}.json", json.dumps(state, ensure_ascii=False, indent=2))
            return state

    cursor = load_cursor(target)
    turns: list[dict] = cursor.get("turns") or []
    conversation_id = cursor.get("conversation_id") or ""
    started_at = cursor.get("started_at") or _now_iso()
    progress_history: list[int] = [t.get("progress_delta", 0) for t in turns]
    wall_clock_start = time.time()

    # ----- Stage 0 (Stage Q): codex+claude multi-round quick path -----
    # Only runs on a clean target — if cursor already has oracle turns or
    # raw_oracle_latex.md is present, that means we've already escalated to
    # Stage 1 (or completed it) on a prior attempt; don't redo Stage 0.
    stage0_summary: dict = cursor.get("stage0") or {}
    raw_latex_path = out_dir / "raw_oracle_latex.md"
    stage0_enabled = not getattr(args, "no_stage0", False)
    stage0_already_ran = bool(stage0_summary) or bool(turns) or raw_latex_path.exists()
    if stage0_enabled and not stage0_already_ran:
        max_rounds = int(getattr(args, "stage0_max_rounds", stage0_quickpath.DEFAULT_MAX_ROUNDS))
        print(
            f"[stage0] {target.target_id} starting quick path (max_rounds={max_rounds})",
            flush=True,
        )
        s0 = stage0_quickpath.run_stage0(target, max_rounds=max_rounds)
        stage0_summary = {
            "verdict": s0.verdict,
            "tex_file": s0.tex_file,
            "rounds": [
                {
                    "round": r.get("round"),
                    "outcome": r.get("outcome"),
                    "codex_verdict": (r.get("codex") or {}).get("verdict"),
                    "review_verdict": (r.get("review") or {}).get("verdict"),
                    "review_score": (r.get("review") or {}).get("score"),
                }
                for r in s0.rounds
            ],
            "rounds_total": len(s0.rounds),
            "reason": s0.reason,
            "error": s0.error,
        }
        write_text(out_dir / "stage0_result.json", json.dumps(stage0_summary, ensure_ascii=False, indent=2))
        cursor["stage0"] = stage0_summary
        save_cursor(target, {
            "turns": turns,
            "started_at": started_at,
            "conversation_id": conversation_id,
            "stage0": stage0_summary,
            "attempts": cursor.get("attempts", 1),
            "crashed_retries": cursor.get("crashed_retries", 0),
        })
        if s0.verdict == "accept" and s0.content.strip():
            # Embed the suggested tex_file as an Insertion target hint so
            # _extract_insertion_target picks it up the same way as the oracle's
            # WRITE_PAPER_LATEX terminal turn would.
            insertion_hint = f"Insertion target: {s0.tex_file}\n\n" if s0.tex_file else ""
            write_text(raw_latex_path, insertion_hint + s0.content.rstrip() + "\n")
            print(
                f"[stage0] {target.target_id} accepted — wrote {raw_latex_path.name} "
                f"({len(s0.content)} chars); skipping Stage 1, going to Stage 2",
                flush=True,
            )
            # Mark a synthetic Stage 1 verdict=done so the rest of run_target
            # (Stage 2 dispatch + final state annotation) flows unchanged.
            verdict_after_stage0 = "done_via_stage0"
        else:
            print(
                f"[stage0] {target.target_id} escalating to Stage 1 oracle: {s0.reason[:200]}",
                flush=True,
            )
            verdict_after_stage0 = ""
    else:
        if stage0_already_ran:
            reason = "cursor has prior turns" if turns else (
                "raw_oracle_latex.md already present" if raw_latex_path.exists() else "stage0 already recorded"
            )
            print(f"[stage0] {target.target_id} skipped ({reason})", flush=True)
        verdict_after_stage0 = ""

    if verdict_after_stage0 != "done_via_stage0":
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
    if verdict_after_stage0 == "done_via_stage0":
        print(
            f"[stage1] skipped: Stage 0 quick-path produced raw_oracle_latex.md; "
            f"jumping directly to Stage 2",
            flush=True,
        )
        verdict = "done"
    elif turns and (turns[-1].get("response_verdict") or "").lower() == "done":
        print(
            f"[stage1] cursor shows turn {turns[-1].get('turn')} already done "
            f"(progress_delta={turns[-1].get('progress_delta')}); "
            f"skipping Stage 1 loop, proceeding to terminal LaTeX",
            flush=True,
        )
        verdict = "done"
    while verdict == "open":
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
            # Userscript races (e.g. waitForResponse capturing the prior assistant
            # message before ChatGPT renders the new one) have made this a
            # frequent transport-side failure rather than a real signal. Mark the
            # turn with a specific verdict, save cursor, and stop the loop —
            # don't crash, and don't auto-retry: lifecycle treats
            # `oracle_duplicate_response` as retry_budget=0 / next_action=skip
            # so the target parks until the userscript bug is addressed.
            duplicate_path = out_dir / f"turn_{turn_idx:02d}_response.duplicate.md"
            write_text(duplicate_path, response)
            print(
                f"[stage1] duplicate response detected for turn {turn_idx} "
                f"(matches turn {duplicate_of}); marking target stuck without retry",
                flush=True,
            )
            turns.append({
                "turn": turn_idx,
                "task_id": task_id,
                "verdict": "duplicate_response",
                "duplicate_of": duplicate_of,
            })
            verdict = "stuck"
            save_cursor(target, {
                "turns": turns,
                "conversation_id": conversation_id,
                "started_at": started_at,
            })
            break

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
    if verdict == "done" and raw_latex_path.exists() and raw_latex_path.stat().st_size > 100:
        print(
            f"[stage1] raw_oracle_latex.md already exists ({raw_latex_path.stat().st_size} bytes) "
            f"from prior attempt; skipping terminal WRITE_PAPER_LATEX, going straight to Stage 1.5/2",
            flush=True,
        )
    elif verdict == "done":
        def _safe_fmt(s: str) -> str:
            return (s or "").replace("{", "{{").replace("}", "}}")
        latex_prompt = WRITE_LATEX_PROMPT_PATH.read_text(encoding="utf-8").format(
            target_id=_safe_fmt(target.target_id),
            target_title=_safe_fmt(target.title),
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

    # ----- Stage 1.5: topic discovery (only if done AND we have oracle turns) -----
    # Stage 0 path produces no oracle transcript — there's nothing for codex
    # to mine, so skip discovery on that path. Adjacent topics will surface
    # through subsequent oracle-routed targets instead.
    spawned_ids: list[str] = []
    if verdict == "done" and turns:
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
    stage2_attempts: list[dict] = []
    if verdict == "done" and raw_latex_path.exists():
        max_stage2_attempts = 2
        for attempt in range(1, max_stage2_attempts + 1):
            suggested = _extract_insertion_target(raw_latex_path.read_text(encoding="utf-8"))
            result = killo_golden_writeback.writeback(
                target_id=target.target_id,
                target_title=target.title,
                transcript_dir=out_dir,
                raw_latex_path=raw_latex_path,
                suggested_target_tex=suggested,
            )
            attempt_record = {
                "attempt": attempt,
                "ok": result.ok,
                "verdict": result.verdict,
                "tex_file": result.tex_file,
                "appended": result.appended,
                "compile_ok": result.compile_ok,
                "rejection_reasons": list(result.rejection_reasons),
                "error": result.error,
            }
            stage2_attempts.append(attempt_record)
            if result.appended and result.compile_ok:
                print(f"[stage2 attempt {attempt}] appended to {result.tex_file} and `make` succeeded", flush=True)
                break
            print(f"[stage2 attempt {attempt}] verdict={result.verdict} appended={result.appended} compile_ok={result.compile_ok}", flush=True)
            if attempt >= max_stage2_attempts:
                break
            if result.verdict != "reject" or not result.rejection_reasons:
                break
            corrective_response = _stage2_corrective_retry(
                args=args,
                target=target,
                conversation_id=conversation_id,
                rejection_reasons=result.rejection_reasons,
                out_dir=out_dir,
                attempt=attempt,
            )
            if corrective_response is None:
                print(f"[stage2 attempt {attempt}] corrective retry skipped (oracle empty / timeout)", flush=True)
                break
            if corrective_response.startswith("DUPLICATE_OF:"):
                label = corrective_response.split(":", 1)[1].strip()
                print(f"[stage2 attempt {attempt}] oracle declared DUPLICATE_OF: {label}; marking already_in_paper", flush=True)
                stage2_summary = {
                    "ok": True,
                    "verdict": "duplicate_of",
                    "duplicate_label": label,
                    "attempts": stage2_attempts,
                }
                verdict = "already_in_paper"
                break
            write_text(out_dir / f"raw_oracle_latex_attempt_{attempt + 1}.md", corrective_response)
            raw_latex_path.write_text(corrective_response, encoding="utf-8")
        if not stage2_summary:
            last = stage2_attempts[-1] if stage2_attempts else {}
            stage2_summary = {
                "ok": last.get("ok", False),
                "verdict": last.get("verdict", "error"),
                "tex_file": last.get("tex_file", ""),
                "appended": last.get("appended", False),
                "compile_ok": last.get("compile_ok", False),
                "rejection_reasons": last.get("rejection_reasons", []),
                "error": last.get("error", ""),
                "attempts": stage2_attempts,
            }
        write_text(out_dir / "stage2_result.json", json.dumps(stage2_summary, ensure_ascii=False, indent=2))

    final_state = {
        "target_id": target.target_id,
        "title": target.title,
        "started_at": started_at,
        "completed_at": _now_iso(),
        "conversation_id": conversation_id,
        "turns": turns,
        "stage0": stage0_summary,
        "stage0_via": (verdict_after_stage0 == "done_via_stage0"),
        "stage1_verdict": verdict,
        "stage15_spawned": spawned_ids,
        "stage2": stage2_summary,
    }
    cursor_attempts = int((cursor.get("attempts") or 1))
    lifecycle.annotate(final_state, attempts=cursor_attempts)
    write_text(STATE_DIR / f"{target.slug}.json", json.dumps(final_state, ensure_ascii=False, indent=2))
    return final_state


# ===========================================================================
# Pipeline v2: codex-track-first + oracle-track-fallback architecture
# ===========================================================================
#
# Major differences vs v1 run_target:
#
#   - Codex track tries FIRST (no 4-round cap; iterates with self-audit and
#     lightweight redline check until close or escalate).
#   - Oracle track only kicks in when codex escalates. Inside the oracle
#     track there is NO progress_delta verdict gate; codex_orchestrator's
#     evaluate_oracle_done() decides done/continue/escalate per turn.
#   - Oracle's initial prompt is the lean Chinese deep-research prompt
#     (oracle_initial.txt), not the v1 boilerplate-heavy build_initial_prompt.
#   - Each oracle follow-up turn embeds a codex-generated dynamic directive
#     (build_oracle_followup_directive).
#   - Stage 1.6 oracle adjacent self-report runs after oracle completes.
#   - Stage 2 corrective: codex_track.run_codex_corrective_track tries to
#     fix hygiene violations BEFORE falling back to oracle corrective.
#   - BOARD spawn merges codex + oracle candidates through a maker/checker
#     judge prompt (board_spawn.spawn_from_candidates).


def _build_oracle_initial_prompt_v2(target: BedcTarget) -> str:
    """Build the lean v2 oracle initial prompt from oracle_initial.txt."""
    template = (SCRIPT_DIR / "prompts" / "oracle_initial.txt").read_text(encoding="utf-8")
    object_str = target.fields.get("Object", target.title)
    problem_str = ""
    # Extract Problem section from BOARD body
    body = target.body or ""
    m = re.search(r"^Problem:\s*\n(.+?)(?:\n\n|\Z)", body, flags=re.MULTILINE | re.DOTALL)
    if m:
        problem_str = m.group(1).strip()
    return template.format(
        target_id=target.target_id,
        target_title=target.title,
        object=object_str,
        problem=problem_str,
    )


def _build_oracle_followup_prompt_v2(*, last_id: int, last_topic_short: str, directive: str) -> str:
    template = (SCRIPT_DIR / "prompts" / "oracle_followup.txt").read_text(encoding="utf-8")
    return template.format(
        last_id=last_id,
        last_topic_short=last_topic_short[:80],
        specific_directive=directive,
    )


def run_target_v2(args: argparse.Namespace, target: BedcTarget) -> dict:
    """Pipeline v2: codex-first, oracle-on-escalate, joint BOARD spawn."""
    out_dir = artifact_dir(target)

    # ---- Pre-flight: prior_art ----
    if not getattr(args, "force", False):
        from prior_art import find_paper_coverage
        coverage = find_paper_coverage(target.fields.get("Object", ""))
        if coverage:
            print(
                f"[v2] target {target.target_id} already covered by paper "
                f"({len(coverage)} hits); skipping",
                flush=True,
            )
            state = {
                "target_id": target.target_id,
                "title": target.title,
                "started_at": _now_iso(),
                "completed_at": _now_iso(),
                "stage1_verdict": "already_in_paper",
                "paper_coverage": coverage[:20],
                "pipeline_version": "v2",
            }
            lifecycle.annotate(state, attempts=int((load_cursor(target).get("attempts") or 1)))
            write_text(STATE_DIR / f"{target.slug}.json", json.dumps(state, ensure_ascii=False, indent=2))
            return state

    cursor = load_cursor(target)
    turns: list[dict] = cursor.get("turns") or []
    conversation_id = cursor.get("conversation_id") or ""
    started_at = cursor.get("started_at") or _now_iso()
    wall_clock_start = time.time()
    raw_latex_path = out_dir / "raw_oracle_latex.md"

    codex_board_candidates: list[dict] = list(cursor.get("codex_board_candidates") or [])
    oracle_board_candidates: list[dict] = list(cursor.get("oracle_board_candidates") or [])

    # ---- Codex track ----
    codex_summary: dict = cursor.get("codex_track") or {}
    codex_already_ran = bool(codex_summary) or bool(turns) or raw_latex_path.exists()
    codex_close_path = bool(codex_summary.get("close_path", False))
    # Resume case: cursor was written under v1 Stage 0 (key: "stage0") with
    # accept verdict OR raw_oracle_latex.md exists from prior closed run.
    # Treat that content as a closed track — do NOT re-engage oracle.
    legacy_stage0 = cursor.get("stage0") or {}
    legacy_stage0_accepted = (
        str(legacy_stage0.get("verdict") or "").lower() == "accept"
    )
    if (not codex_close_path) and not turns and (
        legacy_stage0_accepted or raw_latex_path.exists()
    ):
        codex_close_path = True
        print(
            f"[v2 resume] {target.target_id} treating as closed: "
            f"legacy_stage0_accepted={legacy_stage0_accepted}, "
            f"raw_latex_exists={raw_latex_path.exists()}; skipping oracle.",
            flush=True,
        )
    if not codex_already_ran and not getattr(args, "no_codex_track", False):
        max_rounds = int(getattr(args, "codex_max_rounds", codex_track.DEFAULT_MAX_ROUNDS))
        wall_clock_s = int(getattr(args, "codex_wall_clock_s", codex_track.DEFAULT_WALL_CLOCK_S))
        print(
            f"[v2 codex_track] {target.target_id} starting "
            f"(max_rounds={max_rounds}, wall_clock={wall_clock_s}s)",
            flush=True,
        )
        ct = codex_track.run_codex_track(target, max_rounds=max_rounds, wall_clock_s=wall_clock_s)
        codex_board_candidates.extend(ct.board_candidates)
        close_path = (ct.verdict == "close" and ct.content.strip())
        codex_summary = {
            "verdict": ct.verdict,
            "tex_file": ct.tex_file,
            "rounds_total": len(ct.rounds),
            "rounds_summary": [
                {"round": r.get("round"),
                 "outcome": r.get("outcome"),
                 "codex_verdict": (r.get("codex") or {}).get("verdict"),
                 "audit_score": (r.get("codex") or {}).get("audit_score"),
                 "redline_verdict": (r.get("redline") or {}).get("verdict")}
                for r in ct.rounds
            ],
            "reason": ct.reason,
            "error": ct.error,
            "close_path": close_path,
            "board_candidates_count": len(ct.board_candidates),
        }
        write_text(out_dir / "codex_track_result.json", json.dumps(codex_summary, ensure_ascii=False, indent=2))
        cursor["codex_track"] = codex_summary
        cursor["codex_board_candidates"] = codex_board_candidates
        save_cursor(target, {
            "turns": turns,
            "started_at": started_at,
            "conversation_id": conversation_id,
            "codex_track": codex_summary,
            "codex_board_candidates": codex_board_candidates,
            "attempts": cursor.get("attempts", 1),
            "crashed_retries": cursor.get("crashed_retries", 0),
        })
        codex_close_path = close_path
        if close_path:
            insertion_hint = f"Insertion target: {ct.tex_file}\n\n" if ct.tex_file else ""
            write_text(raw_latex_path, insertion_hint + ct.content.rstrip() + "\n")
            print(
                f"[v2 codex_track] {target.target_id} CLOSE — wrote {raw_latex_path.name} "
                f"({len(ct.content)} chars); skipping oracle, going to Stage 2",
                flush=True,
            )
        else:
            print(
                f"[v2 codex_track] {target.target_id} {ct.verdict}: {ct.reason[:200]}",
                flush=True,
            )

    # ---- Oracle track (only if codex didn't close) ----
    verdict = "open"
    if codex_close_path:
        verdict = "done"
    elif turns and (turns[-1].get("response_verdict") or "").lower() == "done":
        print(
            f"[v2 oracle] cursor shows turn {turns[-1].get('turn')} already done; skipping loop",
            flush=True,
        )
        verdict = "done"

    if verdict == "open":
        # Preflight tab wait (only when actually invoking oracle)
        print_status_hint(args.server)
        if args.preflight_agent_wait > 0 and not wait_for_recent_agent(
            args.server, args.preflight_agent_wait, args.poll_interval
        ):
            raise SystemExit(
                "no active BEDC ChatGPT tab appeared before preflight timeout; "
                "open https://chatgpt.com/?bedc=1 and click Start"
            )

        # Initial prompt: lean v2 if no prior turns, else cursor pending or rebuild
        if not turns:
            prompt = _build_oracle_initial_prompt_v2(target)
        else:
            prompt = cursor.get("pending_prompt") or _build_oracle_initial_prompt_v2(target)

        target_object = target.fields.get("Object", target.title)
        while verdict == "open":
            wall_hours = (time.time() - wall_clock_start) / 3600.0
            if wall_hours >= args.wall_clock_hours:
                print(
                    f"[v2 oracle] wall-clock ceiling {args.wall_clock_hours}h reached; stopping",
                    flush=True,
                )
                verdict = "stuck"
                break

            turn_idx = len(turns)
            task_id = f"bedc_{target.target_id.lower()}_t{turn_idx}_{int(time.time() * 1000)}"
            write_text(out_dir / f"turn_{turn_idx:02d}_prompt.md", prompt)
            # Attach PDF only on first turn of a fresh conversation
            # (no existing conversation_id). Follow-up turns inherit
            # PDF context from earlier turns in the same chat.
            attach_pdf_path = getattr(args, "attach_pdf", None)
            pdf_b64 = ""
            pdf_name = ""
            if attach_pdf_path and not conversation_id and turn_idx == 0:
                pdf_b64, pdf_name = encode_pdf_for_attach(Path(attach_pdf_path))
                if pdf_b64:
                    print(
                        f"[v2 oracle] attaching PDF {pdf_name} "
                        f"({len(pdf_b64) * 0.75 / 1024:.0f} KB) for first-turn",
                        flush=True,
                    )
            submit = submit_turn(
                args.server, task_id, prompt, conversation_id, model=args.model,
                pdf_base64=pdf_b64, pdf_name=pdf_name,
            )
            if "error" in submit:
                raise SystemExit(f"oracle submit failed: {submit['error']}")
            conversation_id = submit.get("conversation_id") or conversation_id
            print(
                f"[v2 oracle] task={task_id} conv={conversation_id[:12]} turn={turn_idx} "
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

            # Duplicate response detection (parked, not crashed)
            duplicate_of = None
            for prev_idx in range(turn_idx):
                prev_path = out_dir / f"turn_{prev_idx:02d}_response.md"
                if prev_path.exists() and prev_path.read_text(encoding="utf-8") == response:
                    duplicate_of = prev_idx
                    break
            if duplicate_of is not None:
                duplicate_path = out_dir / f"turn_{turn_idx:02d}_response.duplicate.md"
                write_text(duplicate_path, response)
                print(
                    f"[v2 oracle] duplicate response at turn {turn_idx} (matches {duplicate_of}); "
                    f"marking stuck without retry",
                    flush=True,
                )
                turns.append({
                    "turn": turn_idx,
                    "task_id": task_id,
                    "verdict": "duplicate_response",
                    "duplicate_of": duplicate_of,
                })
                verdict = "stuck"
                save_cursor(target, {
                    "turns": turns,
                    "conversation_id": conversation_id,
                    "started_at": started_at,
                })
                break

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

            # ---- Codex done-judge (replaces progress_delta gate) ----
            eval_res = codex_orchestrator.evaluate_oracle_done(
                target_id=target.target_id,
                target_title=target.title,
                target_object=target_object,
                history_turns=turns,
                last_response=response,
            )
            if eval_res.ok and eval_res.parsed:
                eval_verdict = str(eval_res.parsed.get("verdict", "continue")).lower()
                contribution = str(eval_res.parsed.get("reason", ""))[:400]
                if eval_verdict == "done":
                    publishable = str(eval_res.parsed.get("publishable_summary", ""))
                    turns.append({
                        "turn": turn_idx,
                        "task_id": task_id,
                        "response_verdict": "done",
                        "contribution_one_liner": contribution,
                        "publishable_summary": publishable,
                    })
                    verdict = "done"
                    save_cursor(target, {
                        "turns": turns,
                        "conversation_id": conversation_id,
                        "started_at": started_at,
                    })
                    break
                elif eval_verdict == "escalate":
                    turns.append({
                        "turn": turn_idx,
                        "task_id": task_id,
                        "response_verdict": "escalate",
                        "contribution_one_liner": contribution,
                    })
                    verdict = "stuck"
                    save_cursor(target, {
                        "turns": turns,
                        "conversation_id": conversation_id,
                        "started_at": started_at,
                    })
                    break
                else:
                    next_directive = str(eval_res.parsed.get("next_directive", ""))
            else:
                print(
                    f"[v2 oracle] codex eval unavailable: {eval_res.error or 'no parsed'}; "
                    f"using fallback directive",
                    flush=True,
                )
                contribution = "(eval unavailable)"
                next_directive = ""

            turns.append({
                "turn": turn_idx,
                "task_id": task_id,
                "response_verdict": "open",
                "contribution_one_liner": contribution,
            })

            # Build next prompt: dynamic followup directive embedded in oracle_followup.txt
            if not next_directive.strip():
                next_directive = codex_orchestrator._fallback_oracle_directive(turns)
            last_topic_short = (turns[-1].get("contribution_one_liner") or "")[:80]
            next_prompt = _build_oracle_followup_prompt_v2(
                last_id=turn_idx,
                last_topic_short=last_topic_short,
                directive=next_directive,
            )
            save_cursor(target, {
                "turns": turns,
                "conversation_id": conversation_id,
                "started_at": started_at,
                "pending_prompt": next_prompt,
            })
            prompt = next_prompt

    # ---- Stage 1.6: oracle adjacent self-report ----
    if verdict == "done" and not codex_close_path and turns and conversation_id:
        try:
            adjacent_prompt = board_spawn.build_oracle_adjacent_prompt(
                target_id=target.target_id, target_title=target.title,
            )
            adj_task_id = f"bedc_{target.target_id.lower()}_adjacent_{int(time.time() * 1000)}"
            write_text(out_dir / "turn_adjacent_prompt.md", adjacent_prompt)
            adj_submit = submit_turn(args.server, adj_task_id, adjacent_prompt, conversation_id, model=args.model)
            if "error" not in adj_submit:
                adj_response = poll_result(
                    args.server, adj_task_id, args.timeout, args.poll_interval, args.status_interval
                )
                if adj_response:
                    write_text(out_dir / "turn_adjacent_response.md", adj_response)
                    parsed = board_spawn.parse_oracle_adjacent_response(adj_response)
                    oracle_board_candidates.extend(parsed)
                    print(
                        f"[v2 stage1.6] oracle returned {len(parsed)} adjacent candidates",
                        flush=True,
                    )
        except Exception as exc:
            print(f"[v2 stage1.6] adjacent self-report skipped: {exc}", flush=True)

    # ---- Terminal LaTeX (only if oracle done and no raw_latex yet) ----
    if verdict == "done" and not codex_close_path and not raw_latex_path.exists():
        def _safe_fmt(s: str) -> str:
            return (s or "").replace("{", "{{").replace("}", "}}")
        latex_prompt = WRITE_LATEX_PROMPT_PATH.read_text(encoding="utf-8").format(
            target_id=_safe_fmt(target.target_id),
            target_title=_safe_fmt(target.title),
        )
        task_id = f"bedc_{target.target_id.lower()}_writelatex_{int(time.time() * 1000)}"
        write_text(out_dir / "turn_writelatex_prompt.md", latex_prompt)
        submit = submit_turn(args.server, task_id, latex_prompt, conversation_id, model=args.model)
        if "error" not in submit:
            print(f"[v2 terminal] WRITE_PAPER_LATEX submitted: {task_id}", flush=True)
            latex_response = poll_result(
                args.server, task_id, args.timeout, args.poll_interval, args.status_interval,
            )
            if latex_response:
                write_text(raw_latex_path, latex_response)
            else:
                print("[v2 terminal] empty response; demoting to stuck", flush=True)
                verdict = "stuck"
        else:
            print(f"[v2 terminal] submit failed: {submit['error']}", flush=True)
            verdict = "stuck"

    # ---- Stage 2: writeback with codex corrective track ----
    stage2_summary: dict = {}
    stage2_attempts: list[dict] = []
    if verdict == "done" and raw_latex_path.exists():
        max_attempts = int(getattr(args, "stage2_max_attempts", 3))
        for attempt in range(1, max_attempts + 1):
            suggested = _extract_insertion_target(raw_latex_path.read_text(encoding="utf-8"))
            result = killo_golden_writeback.writeback(
                target_id=target.target_id,
                target_title=target.title,
                transcript_dir=out_dir,
                raw_latex_path=raw_latex_path,
                suggested_target_tex=suggested,
            )
            attempt_record = {
                "attempt": attempt,
                "ok": result.ok,
                "verdict": result.verdict,
                "tex_file": result.tex_file,
                "appended": result.appended,
                "compile_ok": result.compile_ok,
                "rejection_reasons": list(result.rejection_reasons),
                "compile_errors": list(getattr(result, "compile_errors", None) or []),
                "error": result.error,
            }
            stage2_attempts.append(attempt_record)
            if result.appended and result.compile_ok:
                print(
                    f"[v2 stage2 attempt {attempt}] appended to {result.tex_file} and `make` succeeded",
                    flush=True,
                )
                break
            print(
                f"[v2 stage2 attempt {attempt}] verdict={result.verdict} "
                f"appended={result.appended} compile_ok={result.compile_ok}",
                flush=True,
            )
            if attempt >= max_attempts:
                break

            # Decide whether to invoke codex corrective.
            # - verdict=="reject" with rejection_reasons: classic hygiene/topic reject
            # - verdict=="compile_failed": pdflatex broke; feed compile_errors as reasons
            # - other: nothing useful for codex; break
            corrective_reasons: list[str] = []
            if result.verdict == "reject" and result.rejection_reasons:
                corrective_reasons = list(result.rejection_reasons)
            elif result.verdict == "compile_failed":
                ce = list(getattr(result, "compile_errors", None) or [])
                if ce:
                    corrective_reasons = [
                        "Stage 2 paper compile failed; pdflatex emitted these errors:",
                        *ce,
                        "Please fix the LaTeX so it compiles. Common patterns: "
                        "spacing macro `\\qquad` / `\\quad` / `\\hspace` followed "
                        "immediately by a letter or digit (must have whitespace "
                        "between the control sequence and the next token); "
                        "`$$ ... $$` display math not on its own line; undefined "
                        "control sequence (likely a typo or mashed token).",
                    ]
            if not corrective_reasons:
                break

            # ---- v2 corrective: codex first, oracle fallback ----
            print(
                f"[v2 stage2 attempt {attempt}] running codex corrective track "
                f"(verdict={result.verdict}, {len(corrective_reasons)} reasons)",
                flush=True,
            )
            cc = codex_track.run_codex_corrective_track(
                target,
                original_content=raw_latex_path.read_text(encoding="utf-8"),
                rejection_reasons=corrective_reasons,
            )
            attempt_record["codex_corrective"] = {
                "verdict": cc.verdict,
                "rounds": len(cc.rounds),
                "reason": cc.reason[:300],
            }
            if cc.verdict == "close":
                # Codex fixed it; rewrite raw_latex_path with corrected content
                insertion_hint = f"Insertion target: {cc.tex_file}\n\n" if cc.tex_file else ""
                write_text(raw_latex_path, insertion_hint + cc.content.rstrip() + "\n")
                continue  # next attempt re-runs Stage 2 with fixed content

            if cc.verdict == "duplicate_of":
                stage2_summary = {
                    "ok": True,
                    "verdict": "duplicate_of",
                    "duplicate_label": cc.duplicate_label,
                    "attempts": stage2_attempts,
                }
                verdict = "already_in_paper"
                break

            # codex escalated or exhausted → fall back to oracle corrective (existing path)
            corrective_response = _stage2_corrective_retry(
                args=args,
                target=target,
                conversation_id=conversation_id,
                rejection_reasons=result.rejection_reasons,
                out_dir=out_dir,
                attempt=attempt,
            )
            if corrective_response is None:
                print(
                    f"[v2 stage2 attempt {attempt}] oracle corrective skipped (empty/timeout)",
                    flush=True,
                )
                break
            if corrective_response.startswith("DUPLICATE_OF:"):
                label = corrective_response.split(":", 1)[1].strip()
                stage2_summary = {
                    "ok": True,
                    "verdict": "duplicate_of",
                    "duplicate_label": label,
                    "attempts": stage2_attempts,
                }
                verdict = "already_in_paper"
                break
            write_text(out_dir / f"raw_oracle_latex_attempt_{attempt + 1}.md", corrective_response)
            raw_latex_path.write_text(corrective_response, encoding="utf-8")

        if not stage2_summary:
            last = stage2_attempts[-1] if stage2_attempts else {}
            stage2_summary = {
                "ok": last.get("ok", False),
                "verdict": last.get("verdict", "error"),
                "tex_file": last.get("tex_file", ""),
                "appended": last.get("appended", False),
                "compile_ok": last.get("compile_ok", False),
                "rejection_reasons": last.get("rejection_reasons", []),
                "error": last.get("error", ""),
                "attempts": stage2_attempts,
            }
        write_text(out_dir / "stage2_result.json", json.dumps(stage2_summary, ensure_ascii=False, indent=2))

    # ---- BOARD spawn (combined codex + oracle candidates) ----
    # Only spawn if Stage 2 actually landed in paper. Spawning from a
    # target whose math never made it into the paper risks polluting
    # BOARD with candidates derived from un-vetted reasoning.
    spawned_ids: list[str] = []
    spawn_summary: dict = {}
    stage2_landed = (
        stage2_summary.get("appended", False)
        and stage2_summary.get("compile_ok", False)
    )
    if (verdict == "done" and stage2_landed
            and (codex_board_candidates or oracle_board_candidates)):
        try:
            sr = board_spawn.spawn_from_candidates(
                codex_candidates=codex_board_candidates,
                oracle_candidates=oracle_board_candidates,
            )
            spawn_summary = {
                "ok": sr.ok,
                "appended_ids": sr.appended_ids,
                "accepted_count": len(sr.accepted),
                "rejected_count": len(sr.rejected),
                "error": sr.error,
            }
            spawned_ids = sr.appended_ids
            print(
                f"[v2 board_spawn] codex={len(codex_board_candidates)} "
                f"oracle={len(oracle_board_candidates)} accepted={len(sr.accepted)} "
                f"appended={len(sr.appended_ids)}",
                flush=True,
            )
        except Exception as exc:
            print(f"[v2 board_spawn] failed: {exc}", flush=True)
            spawn_summary = {"ok": False, "error": str(exc)}

    # ---- Final state ----
    final_state = {
        "target_id": target.target_id,
        "title": target.title,
        "started_at": started_at,
        "completed_at": _now_iso(),
        "conversation_id": conversation_id,
        "turns": turns,
        "pipeline_version": "v2",
        "codex_track": codex_summary,
        "codex_close_path": codex_close_path,
        "stage1_verdict": verdict,
        "board_spawn": spawn_summary,
        "stage15_spawned": spawned_ids,
        "stage2": stage2_summary,
    }
    cursor_attempts = int((cursor.get("attempts") or 1))
    lifecycle.annotate(final_state, attempts=cursor_attempts)
    write_text(STATE_DIR / f"{target.slug}.json", json.dumps(final_state, ensure_ascii=False, indent=2))
    return final_state


def _stage2_corrective_retry(
    *,
    args: argparse.Namespace,
    target: BedcTarget,
    conversation_id: str,
    rejection_reasons: list,
    out_dir: Path,
    attempt: int,
) -> str | None:
    """Send rejection_reasons back to the oracle in the same conversation and
    poll for a corrected LaTeX block. Returns the new response or None on
    failure / empty / timeout."""
    if not conversation_id:
        return None
    template_path = SCRIPT_DIR / "prompts" / "write_paper_latex_corrective.txt"
    if not template_path.exists():
        return None
    def _safe(s: str) -> str:
        return (s or "").replace("{", "{{").replace("}", "}}")
    reasons_block = "\n".join(f"- {r}" for r in rejection_reasons)
    try:
        prompt = template_path.read_text(encoding="utf-8").format(
            target_id=_safe(target.target_id),
            target_title=_safe(target.title),
            rejection_reasons=_safe(reasons_block),
        )
    except (IndexError, KeyError) as exc:
        # Template has a stray unescaped brace — log and skip the corrective
        # retry rather than crashing the whole target. Better to land Stage 2
        # reject in final state than lose the worker entirely.
        print(f"[stage2 corrective] template format failure: {exc!r}; skipping retry", flush=True)
        return None
    write_text(out_dir / f"corrective_prompt_attempt_{attempt + 1}.md", prompt)
    task_id = f"bedc_{target.target_id.lower()}_corrective{attempt}_{int(time.time() * 1000)}"
    submit = submit_turn(args.server, task_id, prompt, conversation_id, model=args.model)
    if "error" in submit:
        print(f"[stage2 corrective] submit failed: {submit['error']}", flush=True)
        return None
    response = poll_result(
        args.server,
        task_id,
        args.timeout,
        args.poll_interval,
        args.status_interval,
    )
    if not response:
        return None
    return response


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


STALE_CLAIM_MAX_AGE_SECONDS = 30 * 60


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except (OSError, ProcessLookupError):
        return False


DEFAULT_CRASHED_RETRY_BUDGET = 3


def reset_retriable_crashes(max_retries: int = DEFAULT_CRASHED_RETRY_BUDGET) -> int:
    """Delete crashed final states whose retry budget is not yet exhausted.

    Cursor.json is preserved (so resumed turns are kept) but its
    `crashed_retries` field is bumped. After max_retries the final state
    stays in place and the target is permanently skipped.
    """
    if not STATE_DIR.exists():
        return 0
    reset = 0
    for state_file in STATE_DIR.glob("*.json"):
        try:
            data = json.loads(state_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if data.get("stage1_verdict") != "crashed":
            continue
        slug = state_file.stem
        cursor_path_local = STATE_DIR / slug / "cursor.json"
        retries = 0
        cursor_blob: dict = {}
        if cursor_path_local.exists():
            try:
                cursor_blob = json.loads(cursor_path_local.read_text(encoding="utf-8"))
                retries = int(cursor_blob.get("crashed_retries", 0) or 0)
            except (OSError, json.JSONDecodeError, ValueError):
                cursor_blob = {}
        if retries >= max_retries:
            continue
        cursor_blob["crashed_retries"] = retries + 1
        if cursor_path_local.exists() or cursor_blob.get("turns"):
            try:
                cursor_path_local.parent.mkdir(parents=True, exist_ok=True)
                cursor_path_local.write_text(
                    json.dumps(cursor_blob, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                )
            except OSError:
                pass
        try:
            state_file.unlink()
            reset += 1
            print(
                f"[crash-retry] reset {slug} (retry {retries + 1}/{max_retries})",
                flush=True,
            )
        except OSError:
            pass
    return reset


ORPHAN_PID_REUSE_GRACE_S = 6 * 3600  # only reap a marker as truly orphaned after 6h


def cleanup_stale_claims(max_age_seconds: int = STALE_CLAIM_MAX_AGE_SECONDS) -> int:
    """Remove .in_progress markers whose PID is dead or whose mtime is too old.

    Returns the number of markers cleaned. Safe to call from oracle_client
    startup and from supervisor health checks.
    """
    if not STATE_DIR.exists():
        return 0
    cleaned = 0
    for marker in STATE_DIR.glob("*/.in_progress"):
        try:
            content = marker.read_text(encoding="utf-8")
            age = time.time() - marker.stat().st_mtime
        except OSError:
            continue
        m = re.match(r"pid=(\d+)", content.strip())
        pid_alive = _pid_alive(int(m.group(1))) if m else False
        # Keep markers as long as the recorded PID is alive — long oracle
        # turns (Pro thinking can be 60+ min) and Stage 2 retry cycles can
        # legitimately hold a claim much longer than the legacy 30-min
        # threshold. Only reap when the PID is dead, OR after a hard
        # ORPHAN_PID_REUSE_GRACE_S ceiling (PID could have been recycled by
        # the kernel — mark genuinely abandoned).
        if pid_alive and age <= ORPHAN_PID_REUSE_GRACE_S:
            continue
        try:
            marker.unlink()
            cleaned += 1
            print(
                f"[cleanup] stale claim removed: {marker.parent.name} "
                f"(pid_alive={pid_alive}, age={int(age)}s)",
                flush=True,
            )
        except OSError:
            pass
    return cleaned


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
    """Run a single target; always release its in-progress claim on exit.

    Dispatches to v1 run_target or v2 run_target_v2 based on
    --pipeline-version (default v1 for safety; v2 is the new
    codex-first / oracle-on-escalate architecture).
    """
    try:
        version = getattr(args, "pipeline_version", "v1")
        if version == "v2":
            return run_target_v2(args, target)
        return run_target(args, target)
    except KeyboardInterrupt:
        raise
    except Exception as exc:
        import traceback
        tb = traceback.format_exc()
        print(f"[loop] target {target.target_id} crashed: {exc}\n{tb}", flush=True)
        crash_state = {
            "target_id": target.target_id,
            "title": target.title,
            "stage1_verdict": "crashed",
            "error": str(exc),
            "traceback": tb[-4000:],
            "completed_at": _now_iso(),
        }
        cursor_attempts = int((load_cursor(target).get("attempts") or 1))
        lifecycle.annotate(crash_state, attempts=cursor_attempts)
        write_text(STATE_DIR / f"{target.slug}.json", json.dumps(crash_state, ensure_ascii=False, indent=2))
        return crash_state
    finally:
        release_claim(target)


def run_loop(args: argparse.Namespace) -> int:
    cleaned = cleanup_stale_claims()
    if cleaned:
        print(f"[startup] cleaned {cleaned} stale .in_progress claims", flush=True)
    reset = lifecycle.reset_retriable()
    if reset:
        print(f"[startup] reset {reset} retriable failures (lifecycle-driven)", flush=True)
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
            version = getattr(args, "pipeline_version", "v1")
            if version == "v2":
                run_target_v2(args, target)
            else:
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
    parser.add_argument("--pipeline-version", choices=["v1", "v2"], default="v1",
                        help="v1: legacy Stage 0/1/1.5/2 flow. v2: codex-first track + oracle-on-escalate + joint BOARD spawn (experimental).")
    parser.add_argument("--no-codex-track", action="store_true",
                        help="(v2 only) Disable codex track; route every target straight to oracle.")
    parser.add_argument("--codex-max-rounds", type=int, default=codex_track.DEFAULT_MAX_ROUNDS,
                        help="(v2 only) Round ceiling for codex track (safety net; primary terminator is codex's own verdict).")
    parser.add_argument("--codex-wall-clock-s", type=int, default=codex_track.DEFAULT_WALL_CLOCK_S,
                        help="(v2 only) Wall-clock ceiling for codex track per target (seconds).")
    parser.add_argument("--stage2-max-attempts", type=int, default=3,
                        help="(v2 only) Max Stage 2 writeback attempts (codex corrective + oracle corrective combined).")
    parser.add_argument("--attach-pdf", default="papers/bedc/main.pdf",
                        help="Path to PDF to attach on first oracle turn of each fresh conversation. "
                             "Default: papers/bedc/main.pdf. Set to '' to disable.")
    parser.add_argument("--no-stage0", action="store_true", help="Disable Stage 0 (codex+claude quick path); always go straight to oracle Stage 1")
    parser.add_argument("--stage0-max-rounds", type=int, default=stage0_quickpath.DEFAULT_MAX_ROUNDS, help="Max codex+claude review rounds in Stage 0 before escalating to Stage 1")
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

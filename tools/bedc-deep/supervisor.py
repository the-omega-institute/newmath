#!/usr/bin/env python3
"""BEDC bedc-deep supervisor — outer loop that keeps the pipeline alive.

Wraps `oracle_client.py --loop` and adds:
  1. Server health: ensure bedc_oracle_server.py is running on :8767.
  2. Stale cleanup: prune dead .in_progress markers each pass.
  3. Inner loop manager: spawn oracle_client, restart on crash with backoff.
  4. BOARD low-water: trigger auto_discovery probe when unfinished < threshold.
  5. Curator: trigger after a batch of new completions.
  6. Tab health: alert when queue_waiting_for_browser_agent stays stuck.
  7. Auto-commit: detect changes in papers/bedc/parts/ and BOARD.md, push.
  8. Claude progress review (tier 3): periodic claude -p over the state +
     server snapshot, with recommend_probe / recommend_curator auto-applied.

Stop the supervisor by creating tools/bedc-deep/.stop or sending SIGINT.
On exit, the inner oracle_client is killed cleanly via SIGTERM.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "state"
SUPERVISOR_LOG_DIR = STATE_DIR / "supervisor_logs"
STOP_FILE = SCRIPT_DIR / ".stop"

ORACLE_SERVER_URL = "http://localhost:8767"
SERVER_SCRIPT = SCRIPT_DIR / "bedc_oracle_server.py"
ORACLE_CLIENT = SCRIPT_DIR / "oracle_client.py"
AUTO_DISCOVERY = SCRIPT_DIR / "auto_discovery.py"

DEFAULT_PARALLEL = 3
DEFAULT_POLL_INTERVAL = 60
DEFAULT_LOW_WATER = 3
DEFAULT_PROBE_COOLDOWN_HOURS = 6
DEFAULT_CURATOR_COOLDOWN_HOURS = 12
DEFAULT_CLAUDE_REVIEW_HOURS = 6
DEFAULT_INNER_RESTART_BACKOFF_S = 30
TAB_STUCK_THRESHOLD_S = 300
COMPLETIONS_PER_CURATOR = 5

sys.path.insert(0, str(SCRIPT_DIR))


def _now() -> float:
    return time.time()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def supervisor_log(msg: str) -> None:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(SUPERVISOR_LOG_DIR / "supervisor.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


# ---------------------------------------------------------------------------
# server health
# ---------------------------------------------------------------------------


def server_status(timeout: int = 3) -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception:
        return {}


def server_alive(timeout: int = 3) -> bool:
    return server_status(timeout).get("port") == 8767


def ensure_server() -> int | None:
    if server_alive():
        return None
    supervisor_log("server not responding; spawning bedc_oracle_server.py")
    proc = subprocess.Popen(
        ["python3", str(SERVER_SCRIPT)],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    time.sleep(3)
    if not server_alive():
        supervisor_log("server still not responding after spawn; check manually")
        return None
    supervisor_log(f"server spawned pid={proc.pid}")
    return proc.pid


# ---------------------------------------------------------------------------
# BOARD / state introspection
# ---------------------------------------------------------------------------


def _load_board_targets():
    from dispatch_bedc_target import parse_board
    return parse_board()


def board_unfinished_count() -> int:
    targets = _load_board_targets()
    n = 0
    for t in targets.values():
        if (STATE_DIR / f"{t.slug}.json").exists():
            continue
        if (STATE_DIR / t.slug / ".in_progress").exists():
            continue
        n += 1
    return n


def board_completed_count() -> int:
    if not STATE_DIR.exists():
        return 0
    return sum(1 for p in STATE_DIR.glob("*.json"))


def queue_stuck_too_long(threshold_seconds: int) -> bool:
    s = server_status()
    if s.get("diagnosis") != "queue_waiting_for_browser_agent":
        return False
    queued = s.get("queued_tasks") or []
    return any((t.get("age_seconds") or 0) > threshold_seconds for t in queued)


def stale_cleanup() -> int:
    from oracle_client import cleanup_stale_claims
    return cleanup_stale_claims()


def crash_retry_sweep() -> int:
    from lifecycle import reset_retriable
    return reset_retriable()


_REJECTION_ITEM_RE = re.compile(r"item\s*(\d+)|build\s*invariant|content\s*duplication|non-?LaTeX")


def stage2_reject_clusters(min_count: int = 3) -> dict[str, int]:
    """Count Stage 2 rejection reason categories across all completed targets.

    Returns dict of category → count when count >= min_count.
    Categories are normalized: 'item N' (hygiene checklist item N),
    'build_invariant' (label / undefined macro), 'content_duplication',
    'non_latex_trailing'.
    """
    if not STATE_DIR.exists():
        return {}
    counts: dict[str, int] = {}
    targets_dir = SCRIPT_DIR / "targets"
    if not targets_dir.exists():
        return {}
    for stage2_file in targets_dir.glob("*/stage2_result.json"):
        try:
            data = json.loads(stage2_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if data.get("verdict") != "reject":
            continue
        for reason in data.get("rejection_reasons") or []:
            r = (reason or "").lower()
            cat = "other"
            m = _REJECTION_ITEM_RE.search(r)
            if m and m.group(1):
                cat = f"item_{m.group(1)}"
            elif "build invariant" in r:
                cat = "build_invariant"
            elif "content duplication" in r:
                cat = "content_duplication"
            elif "non-latex" in r or "trailing" in r:
                cat = "non_latex_trailing"
            counts[cat] = counts.get(cat, 0) + 1
    return {k: v for k, v in counts.items() if v >= min_count}


def macos_notify(title: str, body: str) -> None:
    """Send a macOS user-visible notification via osascript. No-op on errors."""
    if sys.platform != "darwin":
        return
    safe_title = title.replace('"', '\\"')
    safe_body = body.replace('"', '\\"')
    script = f'display notification "{safe_body}" with title "{safe_title}"'
    try:
        subprocess.run(
            ["osascript", "-e", script],
            timeout=5,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        pass


# ---------------------------------------------------------------------------
# inner loop manager
# ---------------------------------------------------------------------------


def _active_tab_count() -> int:
    s = server_status()
    if not s:
        return 0
    return len(s.get("active_recent_agents") or [])


def spawn_inner(parallel: int) -> subprocess.Popen:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    tabs = _active_tab_count()
    if tabs > 0 and tabs < parallel:
        supervisor_log(f"clamp --parallel {parallel} → {tabs} (active recent tabs={tabs})")
        parallel = tabs
    elif tabs == 0:
        supervisor_log("no active tabs detected at spawn time; using requested parallel and trusting preflight wait")
    log_handle = open(SUPERVISOR_LOG_DIR / "inner.log", "ab")
    log_handle.write(f"\n=== inner spawn at {_now_iso()} parallel={parallel} ===\n".encode())
    log_handle.flush()
    cmd = [
        "python3",
        str(ORACLE_CLIENT),
        "--loop",
        "--parallel", str(parallel),
        "--preflight-agent-wait", "60",
    ]
    proc = subprocess.Popen(
        cmd,
        cwd=str(REPO_ROOT),
        stdout=log_handle,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    supervisor_log(f"inner loop spawned pid={proc.pid} parallel={parallel}")
    return proc


def stop_inner(inner: subprocess.Popen, grace_seconds: int = 30) -> None:
    if inner.poll() is not None:
        return
    try:
        os.killpg(inner.pid, signal.SIGTERM)
        supervisor_log(f"sent SIGTERM to inner pid={inner.pid}")
    except (ProcessLookupError, OSError):
        return
    try:
        inner.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(inner.pid, signal.SIGKILL)
            supervisor_log(f"escalated to SIGKILL on inner pid={inner.pid}")
        except (ProcessLookupError, OSError):
            pass


# ---------------------------------------------------------------------------
# discovery triggers
# ---------------------------------------------------------------------------


def git_sync_dev() -> bool:
    """Fetch + fast-forward-merge origin/dev into current branch.

    Skips if uncommitted changes exist or merge would conflict. Acquires
    paper_writes lock so a Stage 2 append never races against the merge.
    Returns True iff dev's commits were pulled in.
    """
    status = _git(["status", "--porcelain"])
    if status.stdout.strip():
        return False
    _git(["fetch", "origin", "dev"], capture=False)
    behind = _git(["rev-list", "--count", "HEAD..origin/dev"])
    n = behind.stdout.strip() or "0"
    if n == "0":
        return False
    supervisor_log(f"git_sync_dev: pulling {n} commits from origin/dev")
    from locks import file_lock
    with file_lock("paper_writes"):
        merge = _git(["merge", "--no-edit", "origin/dev"])
    if merge.returncode != 0:
        supervisor_log("git_sync_dev: merge failed (conflict?); aborting merge")
        _git(["merge", "--abort"], capture=False)
        return False
    supervisor_log(f"git_sync_dev: merged origin/dev cleanly ({n} commits)")
    return True


def trigger_probe() -> None:
    git_sync_dev()
    supervisor_log("triggering auto_discovery probe")
    subprocess.Popen(
        ["python3", str(AUTO_DISCOVERY), "probe", "--append"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def trigger_curator() -> None:
    git_sync_dev()
    supervisor_log("triggering auto_discovery curator")
    subprocess.Popen(
        ["python3", str(AUTO_DISCOVERY), "curator", "--append"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


# ---------------------------------------------------------------------------
# auto-commit
# ---------------------------------------------------------------------------


def _git(args: list[str], capture: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        capture_output=capture,
        text=True,
    )


def commit_and_push_if_changed() -> bool:
    # Acquire paper_writes lock so we never commit a partial Stage 2 state
    # (where _append_to_tex has run but _make_paper hasn't decided
    # accept/rollback yet). Stage 2 holds this lock through append + make
    # + potential rollback, so commit only sees a consistent post-Stage-2
    # working tree.
    from locks import file_lock
    with file_lock("paper_writes"):
        diff = _git(["status", "--porcelain", "papers/bedc/parts", "tools/bedc-deep/BOARD.md"])
        if not diff.stdout.strip():
            return False
        files: list[str] = []
        for line in diff.stdout.splitlines():
            parts = line.strip().split(None, 1)
            if len(parts) == 2:
                files.append(parts[1])
        if not files:
            return False
        supervisor_log(f"auto-commit: {len(files)} changed files")
        _git(["add", *files], capture=False)
        msg = f"bedc-deep supervisor: paper writeback batch {_now_iso()}"
        rc = _git(["commit", "-m", msg]).returncode
        if rc != 0:
            supervisor_log("auto-commit: git commit returned non-zero (race or empty)")
            return False
        branch = _git(["branch", "--show-current"]).stdout.strip()
        push = _git(["push", "origin", branch], capture=False)
        if push.returncode != 0:
            supervisor_log(f"auto-commit: push failed rc={push.returncode}")
            return False
    supervisor_log(f"auto-commit + push complete on {branch}")
    return True


# ---------------------------------------------------------------------------
# claude progress reviewer (tier 3)
# ---------------------------------------------------------------------------


def _state_summary_lines(limit: int = 60) -> str:
    rows: list[str] = []
    if not STATE_DIR.exists():
        return "(no state files)"
    for f in sorted(STATE_DIR.glob("*.json"))[:limit]:
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        rows.append(
            f"- {d.get('target_id','?')} {d.get('title','')[:50]} "
            f"v={d.get('stage1_verdict','?')} "
            f"s2={(d.get('stage2') or {}).get('verdict','n/a')}"
        )
    return "\n".join(rows) or "(no completed targets)"


def _extract_json_object(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        candidate = fence.group(1)
    else:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first:last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


def run_claude_review() -> dict | None:
    from killo_golden_writeback import claude_exec
    template = (SCRIPT_DIR / "prompts" / "supervisor_review.txt").read_text(encoding="utf-8")
    s = server_status()
    server_blob = json.dumps(s, ensure_ascii=False, indent=2)[:2000] if s else "(unavailable)"

    def _safe(t: str) -> str:
        return (t or "").replace("{", "{{").replace("}", "}}")

    prompt = template.format(
        ts=_safe(_now_iso()),
        state_summary=_safe(_state_summary_lines()[:6000]),
        server_status=_safe(server_blob),
    )
    ok, stdout, rc = claude_exec(prompt, log_tag="supervisor_review", timeout=900)
    if not ok:
        supervisor_log(f"claude review failed: rc={rc}")
        return None
    parsed = _extract_json_object(stdout)
    if parsed is None:
        supervisor_log("claude review returned no JSON")
    return parsed


def run_pi_review(supervisor_state: dict) -> dict | None:
    """PI agent action-capable review. supervisor_state carries mutable
    cooldowns the PI agent may adjust autonomously."""
    import pi_agent

    def _restart_inner_cb() -> None:
        proc: subprocess.Popen | None = supervisor_state.get("inner")
        if proc is not None and proc.poll() is None:
            stop_inner(proc, grace_seconds=20)
        supervisor_state["inner"] = None

    def _adjust_cooldown_cb(args: dict) -> None:
        if not isinstance(args, dict):
            return
        if "probe_hours" in args:
            try:
                supervisor_state["probe_cooldown_hours"] = float(args["probe_hours"])
            except (TypeError, ValueError):
                pass
        if "curator_hours" in args:
            try:
                supervisor_state["curator_cooldown_hours"] = float(args["curator_hours"])
            except (TypeError, ValueError):
                pass

    callbacks = {
        "restart_inner": _restart_inner_cb,
        "adjust_cooldown": _adjust_cooldown_cb,
    }
    plan = pi_agent.run_review(supervisor_callbacks=callbacks)
    if plan is None:
        supervisor_log("pi_agent returned no plan")
        return None
    supervisor_log(
        f"pi verdict: health={plan.get('loop_health')} "
        f"autonomous={len(plan.get('autonomous_actions') or [])} "
        f"inbox={len(plan.get('human_inbox') or [])} "
        f"concerns={len(plan.get('concerns') or [])}"
    )
    return plan


# ---------------------------------------------------------------------------
# main supervision loop
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC bedc-deep supervisor")
    parser.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL)
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    parser.add_argument("--low-water", type=int, default=DEFAULT_LOW_WATER)
    parser.add_argument("--probe-cooldown-hours", type=float, default=DEFAULT_PROBE_COOLDOWN_HOURS)
    parser.add_argument("--curator-cooldown-hours", type=float, default=DEFAULT_CURATOR_COOLDOWN_HOURS)
    parser.add_argument("--claude-review-hours", type=float, default=DEFAULT_CLAUDE_REVIEW_HOURS)
    parser.add_argument("--no-claude-review", action="store_true")
    parser.add_argument("--no-auto-commit", action="store_true")
    parser.add_argument("--no-dev-sync", action="store_true", help="Skip auto-merging origin/dev at startup and before probe/curator")
    parser.add_argument("--inner-restart-backoff", type=int, default=DEFAULT_INNER_RESTART_BACKOFF_S)
    args = parser.parse_args()

    if STOP_FILE.exists():
        supervisor_log(f"clearing stale STOP_FILE {STOP_FILE}")
        STOP_FILE.unlink()

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    supervisor_log(f"supervisor starting (parallel={args.parallel}, claude_review={'off' if args.no_claude_review else 'on'}, auto_commit={'off' if args.no_auto_commit else 'on'})")

    if not args.no_dev_sync:
        try:
            git_sync_dev()
        except Exception as exc:
            supervisor_log(f"git_sync_dev startup error: {exc}")

    last_probe_ts = 0.0
    last_curator_ts = 0.0
    last_claude_review_ts = 0.0
    last_completed_count = board_completed_count()
    last_tab_alert_ts = 0.0
    inner: subprocess.Popen | None = None

    supervisor_state: dict = {
        "inner": None,
        "probe_cooldown_hours": args.probe_cooldown_hours,
        "curator_cooldown_hours": args.curator_cooldown_hours,
    }

    try:
        while not STOP_FILE.exists():
            ensure_server()

            cleaned = stale_cleanup()
            if cleaned:
                supervisor_log(f"cleaned {cleaned} stale claims")

            retried = crash_retry_sweep()
            if retried:
                supervisor_log(f"reset {retried} crashed targets for retry")

            inner = supervisor_state.get("inner")
            if inner is None or inner.poll() is not None:
                if inner is not None and inner.poll() is not None:
                    rc = inner.poll()
                    supervisor_log(f"inner exited rc={rc}; backoff {args.inner_restart_backoff}s before respawn")
                    time.sleep(args.inner_restart_backoff)
                inner = spawn_inner(args.parallel)
                supervisor_state["inner"] = inner

            unfinished = board_unfinished_count()
            since_probe_h = (_now() - last_probe_ts) / 3600.0
            if unfinished < args.low_water and since_probe_h > supervisor_state["probe_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → probe")
                trigger_probe()
                last_probe_ts = _now()

            done_now = board_completed_count()
            since_curator_h = (_now() - last_curator_ts) / 3600.0
            if done_now - last_completed_count >= COMPLETIONS_PER_CURATOR and since_curator_h > supervisor_state["curator_cooldown_hours"]:
                supervisor_log(f"completions delta={done_now - last_completed_count} → curator")
                trigger_curator()
                last_curator_ts = _now()
                last_completed_count = done_now

            if queue_stuck_too_long(TAB_STUCK_THRESHOLD_S):
                if _now() - last_tab_alert_ts > 600:
                    supervisor_log("tab health: queue_waiting_for_browser_agent > 5min — verify ChatGPT tabs ACTIVE")
                    macos_notify(
                        "BEDC supervisor: tab stuck",
                        "ChatGPT tab stuck > 5 min — open https://chatgpt.com/?bedc=1 and click Start",
                    )
                    last_tab_alert_ts = _now()

            clusters = stage2_reject_clusters()
            if clusters:
                supervisor_log(f"stage2 reject clusters: {clusters} — consider hardening WRITE_PAPER_LATEX prompt")

            if not args.no_auto_commit:
                try:
                    commit_and_push_if_changed()
                except Exception as exc:
                    supervisor_log(f"auto-commit error: {exc}")

            if not args.no_claude_review:
                since_claude_h = (_now() - last_claude_review_ts) / 3600.0
                if since_claude_h > args.claude_review_hours:
                    supervisor_log("running periodic PI agent review")
                    try:
                        plan = run_pi_review(supervisor_state)
                    except Exception as exc:
                        supervisor_log(f"pi review error (continuing): {exc}")
                        plan = None
                    last_claude_review_ts = _now()
                    if plan:
                        for entry in plan.get("autonomous_actions") or []:
                            action = (entry.get("action") or "").strip()
                            if action == "run_probe":
                                last_probe_ts = _now()
                            elif action == "run_curator":
                                last_curator_ts = _now()

            time.sleep(args.poll_interval)
    except KeyboardInterrupt:
        supervisor_log("supervisor interrupted")
    finally:
        final_inner = supervisor_state.get("inner") or inner
        if final_inner is not None:
            stop_inner(final_inner)
        if STOP_FILE.exists():
            try:
                STOP_FILE.unlink()
            except OSError:
                pass
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

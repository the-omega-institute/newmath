#!/usr/bin/env python3
"""BEDC bedc-deep supervisor — outer loop that keeps the pipeline alive.

Mission: keep the paper-research pipeline deriving correct, local BEDC
theorem-site content, refilling BOARD from vetted discovery, and surfacing
closure follow-up candidates without mixing them into theorem writeback.

Wraps `oracle_client.py --loop` and adds:
  1. Server health: ensure bedc_oracle_server.py is running on :8767.
  2. Stale cleanup: prune dead .in_progress markers each pass.
  3. Inner loop manager: spawn oracle_client, restart on crash with backoff.
  4. BOARD low-water: trigger auto_discovery probe when unfinished < threshold.
  5. Curator: trigger after a batch of new completions.
  6. Tab health: alert when queue_waiting_for_browser_agent stays stuck.
  7. Auto-commit: detect changes in papers/bedc/parts/ and BOARD.md, push.
  8. Loning watch: fetch-and-report remote pipeline/closure discipline changes.
  9. Claude progress review (tier 3): periodic claude -p over the state +
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
LONING_WATCH = SCRIPT_DIR / "loning_watch.py"

DEFAULT_PARALLEL = 3
DEFAULT_POLL_INTERVAL = 60
DEFAULT_LOW_WATER = 3
DEFAULT_PROBE_COOLDOWN_HOURS = 6
DEFAULT_CURRICULUM_COOLDOWN_HOURS = 6
DEFAULT_PAPER_REVIEW_COOLDOWN_HOURS = 3
DEFAULT_CURATOR_COOLDOWN_HOURS = 12
DEFAULT_CLAUDE_REVIEW_HOURS = 6
DEFAULT_ORACLE_REFILL_COOLDOWN_HOURS = 0.5
DEFAULT_LONING_WATCH_MINUTES = 15
DEFAULT_INNER_RESTART_BACKOFF_S = 30
TAB_STUCK_THRESHOLD_S = 300
COMPLETIONS_PER_CURATOR = 5

sys.path.insert(0, str(SCRIPT_DIR))


def _now() -> float:
    return time.time()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag_safe() -> str:
    """Filesystem-safe timestamp tag (no colons, no slashes)."""
    return datetime.now().strftime("%Y%m%d_%H%M%S")


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
    'non_latex_trailing', 'line_cap', 'bad_target_file',
    'undefined_macro'.
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
            elif "800" in r or "line cap" in r or "far past" in r or "would exceed" in r:
                cat = "line_cap"
            elif "does not exist" in r and ("target" in r or "file" in r):
                cat = "bad_target_file"
            elif "undefined control sequence" in r or "undefined macro" in r:
                cat = "undefined_macro"
            elif "non-latex" in r or "trailing" in r:
                cat = "non_latex_trailing"
            counts[cat] = counts.get(cat, 0) + 1
    return {k: v for k, v in counts.items() if v >= min_count}


def stage2_reject_advice(clusters: dict[str, int]) -> str:
    cats = set(clusters)
    if cats and cats <= {"line_cap", "bad_target_file"}:
        return "consider splitting or rerouting target files"
    if cats and cats <= {"undefined_macro", "build_invariant"}:
        return "consider hardening compile-hygiene checks"
    return "consider hardening WRITE_PAPER_LATEX prompt"


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


def spawn_inner(parallel: int, *, pipeline_version: str = "v2",
                attach_pdf: str = "",
                codex_parallel: int = 0,
                oracle_parallel: int = 0) -> subprocess.Popen:
    """Spawn the inner --loop. Two modes:

    Two-pool mode (preferred): pass codex_parallel + oracle_parallel.
      - codex pool runs codex_track at high concurrency (no tab dependency).
      - oracle pool drains `.oracle_pending` markers, capped at active tabs.
    Single-pool legacy mode: pass `parallel` only (codex+oracle in one
    worker, capped at tabs).

    Active-tab clamp applies to oracle_parallel (or to single-pool parallel)
    so the oracle path never exceeds available browser agents.
    """
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    # Honor PI v1 adjust_parallel intent if it dropped a file under state/
    parallel_intent_path = SCRIPT_DIR / "state" / ".pi_parallel_intent"
    if parallel_intent_path.exists():
        try:
            new_parallel = int(parallel_intent_path.read_text(encoding="utf-8").strip())
            if 1 <= new_parallel <= 8 and new_parallel != parallel:
                supervisor_log(
                    f"pi_parallel_intent: --parallel {parallel} → {new_parallel}"
                )
                parallel = new_parallel
            parallel_intent_path.unlink()
        except (OSError, ValueError):
            pass

    two_pool = codex_parallel > 0 or oracle_parallel > 0
    tabs = _active_tab_count()

    if two_pool:
        # Cap oracle pool at active tabs (browser-bound). Codex pool is
        # compute-bound, no tab clamp.
        if tabs > 0 and oracle_parallel > tabs:
            supervisor_log(
                f"clamp --oracle-parallel {oracle_parallel} → {tabs} "
                f"(active recent tabs={tabs})"
            )
            oracle_parallel = tabs
        elif tabs == 0:
            supervisor_log(
                "no active tabs at spawn — oracle pool will queue tasks "
                "until tabs come online; codex pool unaffected"
            )
        log_handle = open(SUPERVISOR_LOG_DIR / "inner.log", "ab")
        log_handle.write(
            f"\n=== inner spawn at {_now_iso()} two-pool "
            f"codex_parallel={codex_parallel} oracle_parallel={oracle_parallel} "
            f"pipeline={pipeline_version} ===\n".encode()
        )
        log_handle.flush()
        cmd = [
            "python3",
            str(ORACLE_CLIENT),
            "--loop",
            "--codex-parallel", str(codex_parallel),
            "--oracle-parallel", str(oracle_parallel),
            "--preflight-agent-wait", "60",
            "--pipeline-version", pipeline_version,
            "--attach-pdf", attach_pdf,
        ]
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=log_handle,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        supervisor_log(
            f"inner loop spawned pid={proc.pid} codex_parallel={codex_parallel} "
            f"oracle_parallel={oracle_parallel}"
        )
        return proc

    # Legacy single-pool mode
    if tabs > 0 and tabs < parallel:
        supervisor_log(f"clamp --parallel {parallel} → {tabs} (active recent tabs={tabs})")
        parallel = tabs
    elif tabs == 0:
        supervisor_log("no active tabs detected at spawn time; using requested parallel and trusting preflight wait")
    log_handle = open(SUPERVISOR_LOG_DIR / "inner.log", "ab")
    log_handle.write(f"\n=== inner spawn at {_now_iso()} parallel={parallel} pipeline={pipeline_version} ===\n".encode())
    log_handle.flush()
    cmd = [
        "python3",
        str(ORACLE_CLIENT),
        "--loop",
        "--parallel", str(parallel),
        "--preflight-agent-wait", "60",
        "--pipeline-version", pipeline_version,
        "--attach-pdf", attach_pdf,
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


DEV_SYNC_RESOLVER = SCRIPT_DIR / "dev_sync_resolver.py"


def git_sync_dev() -> bool:
    """Fetch + merge the upstream integration branch (origin/codex-auto-dev
    by default — see dev_sync_resolver.UPSTREAM_BRANCH) with claude-driven
    conflict resolution.

    Spawned as a subprocess so the resolver's module constants (upstream
    branch, validation timeouts, claude path) are read fresh from disk on
    every invocation. This way edits to dev_sync_resolver.py take effect
    on the next sync cycle without restarting supervisor.

    The subprocess prints a JSON status object on stdout. Behaviour:
      - holds paper_writes lock for the whole flow
      - attempts ff/clean merge first
      - on conflict: spawns claude to resolve each non-protected file,
        validates with lake build / check-axioms / bedc_ci audit, hard
        resets on any failure
      - protected files (lean4/, papers/main.tex, etc.) abort and report
        to human_inbox via supervisor log
      - commits + pushes on full success

    Returns True iff upstream commits were actually pulled in (ff_merged
    or auto_resolved). On any other outcome returns False — caller should
    treat as "no sync this cycle" and retry later.
    """
    try:
        proc = subprocess.run(
            ["python3", str(DEV_SYNC_RESOLVER)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=2400,  # 40 min: claude resolve + lake build + pdflatex
        )
    except subprocess.TimeoutExpired:
        supervisor_log("git_sync_dev: resolver subprocess timed out (40 min)")
        return False
    except Exception as exc:
        supervisor_log(f"git_sync_dev: resolver subprocess failed to launch: {exc}")
        return False

    raw_stdout = (proc.stdout or "").strip()
    raw_stderr = (proc.stderr or "").strip()
    try:
        result = json.loads(raw_stdout)
    except json.JSONDecodeError:
        supervisor_log(
            f"git_sync_dev: resolver output not JSON (rc={proc.returncode}). "
            f"stdout={raw_stdout[:300]}  stderr={raw_stderr[:300]}"
        )
        return False

    status = result.get("status", "error")
    if status == "up_to_date":
        return False
    if status == "ff_merged":
        n = result.get("n_dev_commits", "?")
        supervisor_log(f"git_sync_dev: ff-merged upstream cleanly ({n} commits)")
        return True
    if status == "auto_resolved":
        n = result.get("n_dev_commits", "?")
        resolved = result.get("resolved_files") or []
        validation = (result.get("validation") or {}).get("summary", "?")
        supervisor_log(
            f"git_sync_dev: auto-resolved {len(resolved)} conflict(s) "
            f"({n} commits); validation={validation}"
        )
        return True
    if status == "aborted_protected":
        files = result.get("conflict_files") or []
        err = result.get("error") or ""
        supervisor_log(
            f"git_sync_dev: ABORTED — protected files in conflict ({err}). "
            f"This needs human attention. Files: {files}"
        )
        return False
    if status == "aborted_validation":
        validation = result.get("validation") or {}
        fails = "; ".join((validation.get("failures") or [])[:1])[:300]
        supervisor_log(
            f"git_sync_dev: ABORTED — validation failed after resolution. "
            f"Hard-reset to ORIG_HEAD. Will retry next cycle. {fails}"
        )
        return False
    if status == "skipped_dirty":
        # quiet — common case during active Stage 2 / normal pipeline life
        return False
    err = result.get("error") or "(no error message)"
    supervisor_log(f"git_sync_dev: error — {err[:300]}")
    return False


def trigger_probe(*, no_dev_sync: bool = False) -> None:
    if not no_dev_sync:
        git_sync_dev()
    supervisor_log("triggering auto_discovery probe")
    # Capture output so silent crashes (e.g. prompt format() KeyError) are
    # visible in the supervisor logs instead of vanishing into DEVNULL.
    log_path = SUPERVISOR_LOG_DIR / f"probe_{_now_tag_safe()}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            ["python3", str(AUTO_DISCOVERY), "probe", "--append"],
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def trigger_curriculum_probe(*, no_dev_sync: bool = False) -> None:
    """Curriculum-aware probe — find textbook-classical theorems missing
    from started chapters. Complements `probe` (internal symmetry gaps)
    and `oracle_board_refill` (deep structural / classification theorems).
    Same architecture as probe but with a different prompt that asks for
    'what would a standard textbook on this object also cover'.
    """
    if not no_dev_sync:
        git_sync_dev()
    supervisor_log("triggering auto_discovery curriculum probe")
    log_path = SUPERVISOR_LOG_DIR / f"curriculum_{_now_tag_safe()}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            ["python3", str(AUTO_DISCOVERY), "curriculum", "--append"],
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def trigger_paper_review(*, no_dev_sync: bool = False) -> None:
    """Editorial-referee audit (paper-driven discovery, gated by our
    judge). Complements `probe` (internal symmetry), `curriculum`
    (textbook-classical), and `oracle_board_refill` (PDF-attached deep
    suggestions). Adapts loning's REVIEW phase but routes through our
    board_judge so candidates land on BOARD only after the same
    fit/novelty/dedup thresholds.
    """
    if not no_dev_sync:
        git_sync_dev()
    supervisor_log("triggering auto_discovery paper_review")
    log_path = SUPERVISOR_LOG_DIR / f"paper_review_{_now_tag_safe()}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            ["python3", str(AUTO_DISCOVERY), "paper_review", "--append"],
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def trigger_oracle_board_refill() -> None:
    """Ask oracle (with project-attached PDF) for new BOARD candidates.

    Complementary to auto_discovery probe: probe finds mechanical gaps via
    codex static scan, oracle_board_refill leverages the full PDF + research
    intuition to suggest deeper directions. Run when BOARD unfinished count
    is low and probe alone isn't refilling.
    """
    supervisor_log("triggering oracle_board_refill")
    log_path = SUPERVISOR_LOG_DIR / f"refill_{_now_tag_safe()}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            ["python3", str(SCRIPT_DIR / "oracle_board_refill.py")],
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def run_loning_watch() -> dict | None:
    """Fetch-and-report loning-side pipeline/closure changes.

    This intentionally does not call git_sync_dev(): the watch path observes
    remote integration branches and writes state/human-inbox notes only.
    """
    try:
        proc = subprocess.run(
            ["python3", str(LONING_WATCH)],
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired:
        supervisor_log("loning_watch: timed out")
        return None
    except OSError as exc:
        supervisor_log(f"loning_watch: failed to launch: {exc}")
        return None
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "").strip()
        supervisor_log(f"loning_watch: rc={proc.returncode} {err[:300]}")
        return None
    try:
        data = json.loads(proc.stdout.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        supervisor_log(f"loning_watch: output not JSON: {(proc.stdout or '')[:300]}")
        return None
    supervisor_log(
        f"loning_watch: refs={len(data.get('refs_checked') or [])} "
        f"new={data.get('new_commits')} relevant={data.get('relevant_commits')}"
    )
    return data


def trigger_curator(*, no_dev_sync: bool = False) -> None:
    if not no_dev_sync:
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
# PI agent review (delegated to pi_agent_v1)
# ---------------------------------------------------------------------------


def run_pi_review(supervisor_state: dict) -> dict | None:
    """PI agent action-capable review. supervisor_state carries mutable
    cooldowns the PI agent may adjust autonomously.

    Always dispatches to pi_agent_v1 (maker/checker gauntlet with the
    expanded action surface). The earlier observer-only v0 was retired
    after v1 stabilised; its shared helpers live in pi_common.py.
    """
    import pi_agent_v1 as pi_module

    def _restart_inner_cb() -> str | None:
        proc: subprocess.Popen | None = supervisor_state.get("inner")
        if proc is not None and proc.poll() is None:
            stop_inner(proc, grace_seconds=20)
        supervisor_state["inner"] = None
        return "inner stopped; supervisor will respawn"

    def _adjust_cooldown_cb(args: dict) -> str | None:
        if not isinstance(args, dict):
            return "args not dict"
        applied = []
        if "probe_hours" in args:
            try:
                supervisor_state["probe_cooldown_hours"] = float(args["probe_hours"])
                applied.append(f"probe={args['probe_hours']}")
            except (TypeError, ValueError):
                pass
        if "curator_hours" in args:
            try:
                supervisor_state["curator_cooldown_hours"] = float(args["curator_hours"])
                applied.append(f"curator={args['curator_hours']}")
            except (TypeError, ValueError):
                pass
        if "pi_hours" in args:
            try:
                supervisor_state["pi_cooldown_hours"] = float(args["pi_hours"])
                applied.append(f"pi={args['pi_hours']}")
            except (TypeError, ValueError):
                pass
        if "oracle_refill_hours" in args:
            try:
                supervisor_state["oracle_refill_cooldown_hours"] = float(args["oracle_refill_hours"])
                applied.append(f"oracle_refill={args['oracle_refill_hours']}")
            except (TypeError, ValueError):
                pass
        return ", ".join(applied) or "no recognized cooldown keys"

    callbacks = {
        "restart_inner": _restart_inner_cb,
        "adjust_cooldown": _adjust_cooldown_cb,
    }
    plan = pi_module.run_review(supervisor_callbacks=callbacks)
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
    parser.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL,
                        help="Single-pool legacy mode: codex+oracle workers in one pool. Set this OR (--codex-parallel + --oracle-parallel), not both.")
    parser.add_argument("--codex-parallel", type=int, default=0,
                        help="Two-pool mode: codex_track workers (compute-bound, no tab dep). Recommended 6-8.")
    parser.add_argument("--oracle-parallel", type=int, default=0,
                        help="Two-pool mode: oracle path workers (drains .oracle_pending, capped at active tabs). Recommended 3.")
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    parser.add_argument("--low-water", type=int, default=DEFAULT_LOW_WATER)
    parser.add_argument("--probe-cooldown-hours", type=float, default=DEFAULT_PROBE_COOLDOWN_HOURS)
    parser.add_argument("--curriculum-cooldown-hours", type=float, default=DEFAULT_CURRICULUM_COOLDOWN_HOURS,
                        help="Cooldown between curriculum probe runs (textbook-classical theorem hunt). "
                             "Complements --probe-cooldown-hours (internal symmetry gaps).")
    parser.add_argument("--paper-review-cooldown-hours", type=float, default=DEFAULT_PAPER_REVIEW_COOLDOWN_HOURS,
                        help="Cooldown between paper_review probe runs (editorial-referee audit, "
                             "loning-style REVIEW gated by our judge).")
    parser.add_argument("--curator-cooldown-hours", type=float, default=DEFAULT_CURATOR_COOLDOWN_HOURS)
    parser.add_argument("--claude-review-hours", type=float, default=DEFAULT_CLAUDE_REVIEW_HOURS)
    parser.add_argument("--oracle-refill-cooldown-hours", type=float, default=DEFAULT_ORACLE_REFILL_COOLDOWN_HOURS,
                        help="Cooldown between oracle_board_refill runs. Triggered alongside probe when BOARD is low water; "
                             "leverages project-attached PDF for deeper candidate suggestions.")
    parser.add_argument("--loning-watch-minutes", type=float, default=DEFAULT_LONING_WATCH_MINUTES,
                        help="Cooldown between fetch-and-report checks of loning-side integration branches.")
    parser.add_argument("--no-loning-watch", action="store_true",
                        help="Disable loning-side fetch-and-report monitoring.")
    parser.add_argument("--no-claude-review", action="store_true")
    # --pi-version was removed when v0 retired; accept-and-ignore for any
    # call sites still passing it.
    parser.add_argument("--pi-version", choices=["v0", "v1"], default="v1",
                        help=argparse.SUPPRESS)
    # --pipeline-version was removed when v1 retired; accept-and-ignore for
    # backward compat with existing launch scripts.
    parser.add_argument("--pipeline-version", choices=["v1", "v2"], default="v2",
                        help=argparse.SUPPRESS)
    parser.add_argument("--attach-pdf", default="",
                        help="PDF path to attach on first oracle turn of fresh conversations. "
                             "Default empty (skip — assumes you're using a ChatGPT Project with "
                             "main.pdf attached at project level, which is more robust). "
                             "Set to e.g. 'papers/bedc/main.pdf' to enable userscript-side upload.")
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
    last_curriculum_ts = 0.0
    last_curator_ts = 0.0
    last_claude_review_ts = 0.0
    last_oracle_refill_ts = 0.0
    last_paper_review_ts = 0.0
    last_loning_watch_ts = 0.0
    last_completed_count = board_completed_count()
    last_tab_alert_ts = 0.0
    inner: subprocess.Popen | None = None

    supervisor_state: dict = {
        "inner": None,
        "probe_cooldown_hours": args.probe_cooldown_hours,
        "curriculum_cooldown_hours": args.curriculum_cooldown_hours,
        "paper_review_cooldown_hours": args.paper_review_cooldown_hours,
        "curator_cooldown_hours": args.curator_cooldown_hours,
        "pi_cooldown_hours": args.claude_review_hours,
        "oracle_refill_cooldown_hours": args.oracle_refill_cooldown_hours,
        "pipeline_version": args.pipeline_version,
        "attach_pdf": args.attach_pdf,
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
                inner = spawn_inner(
                    args.parallel,
                    pipeline_version=supervisor_state.get("pipeline_version", "v2"),
                    attach_pdf=supervisor_state.get("attach_pdf", ""),
                    codex_parallel=getattr(args, "codex_parallel", 0) or 0,
                    oracle_parallel=getattr(args, "oracle_parallel", 0) or 0,
                )
                supervisor_state["inner"] = inner

            unfinished = board_unfinished_count()
            since_probe_h = (_now() - last_probe_ts) / 3600.0
            since_curriculum_h = (_now() - last_curriculum_ts) / 3600.0
            since_oracle_refill_h = (_now() - last_oracle_refill_ts) / 3600.0
            since_paper_review_h = (_now() - last_paper_review_ts) / 3600.0
            if unfinished < args.low_water and since_probe_h > supervisor_state["probe_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → probe")
                trigger_probe(no_dev_sync=args.no_dev_sync)
                last_probe_ts = _now()
            if unfinished < args.low_water and since_curriculum_h > supervisor_state["curriculum_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → curriculum probe")
                trigger_curriculum_probe(no_dev_sync=args.no_dev_sync)
                last_curriculum_ts = _now()
            if unfinished < args.low_water and since_paper_review_h > supervisor_state["paper_review_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → paper_review")
                trigger_paper_review(no_dev_sync=args.no_dev_sync)
                last_paper_review_ts = _now()
            if unfinished < args.low_water and since_oracle_refill_h > supervisor_state["oracle_refill_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → oracle_board_refill")
                trigger_oracle_board_refill()
                last_oracle_refill_ts = _now()

            done_now = board_completed_count()
            since_curator_h = (_now() - last_curator_ts) / 3600.0
            if done_now - last_completed_count >= COMPLETIONS_PER_CURATOR and since_curator_h > supervisor_state["curator_cooldown_hours"]:
                supervisor_log(f"completions delta={done_now - last_completed_count} → curator")
                trigger_curator(no_dev_sync=args.no_dev_sync)
                last_curator_ts = _now()
                last_completed_count = done_now

            if queue_stuck_too_long(TAB_STUCK_THRESHOLD_S):
                if _now() - last_tab_alert_ts > 600:
                    supervisor_log("tab health: queue_waiting_for_browser_agent > 5min — verify ChatGPT tabs ACTIVE")
                    macos_notify(
                        "BEDC supervisor: tab stuck",
                        "ChatGPT tab stuck > 5 min — open https://chatgpt.com/g/g-p-69f750c45b248191ac36b1cd6235f336-bedc/project?bedc=1 and click Start",
                    )
                    last_tab_alert_ts = _now()

            clusters = stage2_reject_clusters()
            if clusters:
                supervisor_log(f"stage2 reject clusters: {clusters} — {stage2_reject_advice(clusters)}")

            if not args.no_loning_watch:
                since_loning_watch_m = (_now() - last_loning_watch_ts) / 60.0
                if since_loning_watch_m > args.loning_watch_minutes:
                    run_loning_watch()
                    last_loning_watch_ts = _now()

            if not args.no_auto_commit:
                try:
                    commit_and_push_if_changed()
                except Exception as exc:
                    supervisor_log(f"auto-commit error: {exc}")

            if not args.no_claude_review:
                since_claude_h = (_now() - last_claude_review_ts) / 3600.0
                if since_claude_h > supervisor_state.get("pi_cooldown_hours", args.claude_review_hours):
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

#!/usr/bin/env python3
"""BEDC bedc-deep supervisor — outer loop that keeps the pipeline alive.

Mission: keep the paper-research pipeline deriving correct, local BEDC
theorem-site content, refilling BOARD from vetted discovery, and surfacing
closure follow-up candidates without mixing them into theorem writeback.

Wraps `oracle_client.py --loop` and adds:
  1. Server health: ensure bedc_oracle_server.py is running on :8767.
  2. Stale cleanup: prune dead .in_progress markers each pass.
  3. Inner loop manager: spawn oracle_client, restart on crash with backoff.
  4. BOARD low-water: trigger paper-native refill/review when unfinished < threshold.
  5. Curator/probe discovery is opt-in only because legacy discovery surfaces
     may inspect non-paper axes; the default supervisor must remain paper-native.
  6. Tab health: alert when queue_waiting_for_browser_agent stays stuck.
  7. Auto-commit: detect changes in papers/bedc/parts/ and BOARD.md, push.
  8. Loning watch: fetch-and-report remote pipeline/closure discipline changes.
  9. PI progress review: periodic pipeline-state review, with
     recommend_probe / recommend_curator auto-applied.

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
NETWORK_RESUME_FILE = STATE_DIR / "network_resume.json"
REQUIRED_BRANCH = "bedc-claim-packet-pipeline"

ORACLE_SERVER_URL = "http://localhost:8767"
SERVER_SCRIPT = SCRIPT_DIR / "bedc_oracle_server.py"
ORACLE_CLIENT = SCRIPT_DIR / "oracle_client.py"
AUTO_DISCOVERY = SCRIPT_DIR / "auto_discovery.py"
LONING_WATCH = SCRIPT_DIR / "loning_watch.py"
LONING_ASSIMILATOR = SCRIPT_DIR / "loning_assimilator.py"
PLAIN_MATH_REVIEW = SCRIPT_DIR / "plain_math_review.py"
RESEARCH_CANDIDATE_LANE = SCRIPT_DIR / "research_candidate_lane.py"

DEFAULT_PARALLEL = 3
DEFAULT_CODEX_PARALLEL = 6
DEFAULT_ORACLE_PARALLEL = 2
DEFAULT_POLL_INTERVAL = 60
DEFAULT_LOW_WATER = 3
DEFAULT_PROBE_COOLDOWN_HOURS = 6
DEFAULT_CURRICULUM_COOLDOWN_HOURS = 6
DEFAULT_PAPER_REVIEW_COOLDOWN_HOURS = 3
DEFAULT_CURATOR_COOLDOWN_HOURS = 12
DEFAULT_CLAUDE_REVIEW_HOURS = 6
DEFAULT_ORACLE_REFILL_COOLDOWN_HOURS = 0.5
DEFAULT_RESEARCH_LANE_COOLDOWN_HOURS = 1.0
DEFAULT_ORACLE_REFILL_RESEARCH_GRACE_MINUTES = 20.0
DEFAULT_DEV_SYNC_COOLDOWN_MINUTES = 15
DEFAULT_DEV_SYNC_ENABLED = True
DEFAULT_DEV_SYNC_TIMEOUT_SECONDS = 600
STARTUP_DEV_SYNC_TIMEOUT_SECONDS = 120
ORPHAN_PID_REUSE_GRACE_S = 6 * 3600
DEFAULT_LONING_WATCH_MINUTES = 15
DEFAULT_INNER_RESTART_BACKOFF_S = 30
DEFAULT_ALLOW_LEAN_ADJACENT_DISCOVERY = False
DEFAULT_ALLOW_ORACLE_CANDIDATE_GENERATION = False
TAB_STUCK_THRESHOLD_S = 300
ZERO_EXTRACTION_ALERT_COOLDOWN_S = 600
ZERO_EXTRACTION_HANG_SECONDS = 900
ZERO_EXTRACTION_MIN_PAGE_CHARS = 1000
CANDIDATE_INBOX_STALE_SECONDS = 2 * 3600
CANDIDATE_INBOX_ALERT_COOLDOWN_S = 30 * 60
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


def assert_required_branch() -> bool:
    result = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    branch = result.stdout.strip()
    if result.returncode != 0 or branch != REQUIRED_BRANCH:
        supervisor_log(
            f"branch guard: refusing to run on {branch or '?'}; "
            f"expected {REQUIRED_BRANCH}"
        )
        return False
    return True


def assert_required_branch_quiet() -> bool:
    result = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    return result.returncode == 0 and result.stdout.strip() == REQUIRED_BRANCH


def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False


def _write_network_resume_checkpoint(kind: str, branch: str, reason: str,
                                     *, head: str = "", upstream: str = "") -> None:
    """Persist a resume marker for network-bound work.

    The critical case is: auto-commit succeeded, git push failed because the
    network dropped. The working tree is then clean, so the normal
    "commit if changed" path will not retry. This checkpoint lets later
    supervisor ticks notice that HEAD is still ahead of its upstream and
    retry the push after connectivity returns.
    """
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    payload = {
        "kind": kind,
        "branch": branch,
        "head": head,
        "upstream": upstream,
        "reason": reason[:1000],
        "updated_at": _now_iso(),
    }
    if NETWORK_RESUME_FILE.exists():
        try:
            old = json.loads(NETWORK_RESUME_FILE.read_text(encoding="utf-8"))
            if isinstance(old, dict) and old.get("created_at"):
                payload["created_at"] = old["created_at"]
        except (OSError, json.JSONDecodeError):
            pass
    payload.setdefault("created_at", payload["updated_at"])
    NETWORK_RESUME_FILE.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _clear_network_resume_checkpoint() -> None:
    try:
        NETWORK_RESUME_FILE.unlink()
    except FileNotFoundError:
        pass
    except OSError as exc:
        supervisor_log(f"network-resume: failed to clear checkpoint: {exc}")


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


def supervisor_status_snapshot() -> dict:
    targets = _load_board_targets()
    active: list[dict] = []
    for t in targets.values():
        final_state = STATE_DIR / f"{t.slug}.json"
        marker = STATE_DIR / t.slug / ".in_progress"
        pending = STATE_DIR / t.slug / ".oracle_pending"
        if final_state.exists():
            continue
        rec = {
            "target_id": t.target_id,
            "title": t.title,
            "slug": t.slug,
            "in_progress": marker.exists(),
            "oracle_pending": pending.exists(),
        }
        if marker.exists():
            try:
                content = marker.read_text(encoding="utf-8").strip()
                age = int(time.time() - marker.stat().st_mtime)
            except OSError:
                content = ""
                age = -1
            m = re.match(r"pid=(\d+)", content)
            pid = int(m.group(1)) if m else 0
            claim_pid_alive = pid_alive(pid) if pid else False
            rec.update({
                "claim": content,
                "claim_age_seconds": age,
                "claim_pid_alive": claim_pid_alive,
                "stale_claim": (not claim_pid_alive) or age > ORPHAN_PID_REUSE_GRACE_S,
            })
        active.append(rec)
    return {
        "branch_ok": assert_required_branch_quiet(),
        "stop_file": STOP_FILE.exists(),
        "server_alive": server_alive(timeout=1),
        "unfinished_unclaimed": board_unfinished_count(),
        "completed_state_files": board_completed_count(),
        "active_targets": active,
    }


def queue_stuck_too_long(threshold_seconds: int) -> bool:
    s = server_status()
    if s.get("diagnosis") != "queue_waiting_for_browser_agent":
        return False
    queued = s.get("queued_tasks") or []
    return any((t.get("age_seconds") or 0) > threshold_seconds for t in queued)


def zero_extraction_hang_agents(status: dict) -> list[str]:
    agents = [str(aid) for aid in (status.get("zero_extraction_hang_agents") or [])]
    if agents:
        return agents
    out: list[str] = []
    active_tasks = {
        str(agent_id): str((task or {}).get("task_id") or "")
        for agent_id, task in (status.get("agents") or {}).items()
    }
    for agent_id, rec in (status.get("recent_agents") or {}).items():
        agent_id = str(agent_id)
        if not active_tasks.get(agent_id):
            continue
        if rec.get("event") != "heartbeat" or not rec.get("recent", False):
            continue
        metrics = rec.get("metrics") or {}
        if str(metrics.get("task_id") or "") != active_tasks[agent_id]:
            continue
        try:
            elapsed = int(metrics.get("elapsed_seconds") or 0)
            extracted = int(metrics.get("extracted_chars") or 0)
            page_chars = int(metrics.get("page_chars") or 0)
        except (TypeError, ValueError):
            continue
        if (
            elapsed >= ZERO_EXTRACTION_HANG_SECONDS
            and extracted == 0
            and page_chars >= ZERO_EXTRACTION_MIN_PAGE_CHARS
        ):
            out.append(agent_id)
    return out


def zero_extraction_hang_details(status: dict) -> list[dict[str, str]]:
    agents = zero_extraction_hang_agents(status)
    details: list[dict[str, str]] = []
    recent = status.get("recent_agents") or {}
    for agent_id in agents:
        rec = recent.get(agent_id) or {}
        metrics = rec.get("metrics") or {}
        details.append(
            {
                "agent_id": agent_id,
                "task_id": str(metrics.get("task_id") or (status.get("agents") or {}).get(agent_id, {}).get("task_id") or ""),
                "url_tail": str(metrics.get("url_tail") or ""),
                "chatgpt_url": str(metrics.get("chatgpt_url") or metrics.get("page_url") or ""),
            }
        )
    return details


def candidate_inbox_health() -> dict:
    try:
        import candidate_inbox
        return candidate_inbox.stats(since_hours=2)
    except Exception as exc:
        return {"error": str(exc)}


NON_MATERIAL_REFINEMENT_REASON_RE = re.compile(
    r"predicted_line_cap_overflow|duplicate_title|structural_title|"
    r"missing_title|missing_claim|claim_too_short|"
    r"forbidden_axis_or_marker_candidate|conjecture_fallback_not_board_lane|"
    r"non_paper_local_input|inspiration_only_not_board_landing|"
    r"external_signal_landing_reject",
    re.IGNORECASE,
)


def candidate_inbox_has_refinement_backlog(inbox_health: dict) -> bool:
    """True when local candidate supply still has material to re-read.

    A low-water supervisor should first spend this backlog through
    plain_math_review/research_candidate_lane before asking the oracle for a
    fresh BOARD refill. This is a scheduling preference only; final BOARD
    admission still goes through board_spawn and writeback gates.
    """
    by_event = inbox_health.get("by_event") or {}
    for key in ("pre_gate_hold", "held_for_refinement"):
        try:
            if int(by_event.get(key) or 0) > 0:
                break
        except (TypeError, ValueError):
            continue
    else:
        return False
    reasons = inbox_health.get("refinement_reasons") or []
    material_seen = False
    for rec in reasons:
        reason = str((rec or {}).get("reason") or "")
        try:
            count = int((rec or {}).get("count") or 0)
        except (TypeError, ValueError):
            count = 0
        if count <= 0:
            continue
        if NON_MATERIAL_REFINEMENT_REASON_RE.search(reason):
            continue
        material_seen = True
        break
    return material_seen


def should_defer_oracle_refill_for_research(
    *,
    research_lane_triggered: bool,
    inbox_health: dict,
    since_research_lane_m: float,
    grace_minutes: float,
) -> tuple[bool, str]:
    if research_lane_triggered:
        return True, "local_research_lane_triggered"
    if not candidate_inbox_has_refinement_backlog(inbox_health):
        return False, "no_material_refinement_backlog"
    if since_research_lane_m < grace_minutes:
        return True, "material_refinement_backlog_within_grace"
    return False, "material_refinement_backlog_grace_elapsed"


def candidate_inbox_source_age_summary(inbox_health: dict) -> str:
    latest = inbox_health.get("latest_by_source_sampled") or {}
    keys = ("oracle_board_refill", "oracle", "paper_review", "direct_append")
    parts: list[str] = []
    for key in keys:
        rec = latest.get(key) or {}
        age = rec.get("age_seconds")
        event = rec.get("event") or "?"
        try:
            age_s = int(age)
        except (TypeError, ValueError):
            continue
        parts.append(f"{key}:{age_s}s/{event}")
    return ",".join(parts)


def stale_cleanup() -> int:
    from oracle_client import cleanup_stale_claims
    return cleanup_stale_claims()


def board_archive_completed() -> int:
    import board_archive
    result = board_archive.prune_completed_board()
    return result.moved


def crash_retry_sweep() -> int:
    from lifecycle import reset_retriable
    return reset_retriable()


def stage2_reject_clusters(min_count: int = 3, window_hours: float = 2.0) -> dict[str, int]:
    """Count Stage 2 rejection reason categories from RECENT completed targets.

    Only stage2_result.json files modified within `window_hours` are counted,
    so PI's signal stays fresh — old failed backlog (alert_user / abandoned
    targets) doesn't keep firing the recurring-pattern trigger after the
    underlying root cause is fixed.

    Returns dict of category → count when count >= min_count. Categories are
    semantic enough for PI advice: line-cap/routing failures should not be
    collapsed with transport-discipline or LaTeX-layout prompt failures.
    """
    if not STATE_DIR.exists():
        return {}
    counts: dict[str, int] = {}
    targets_dir = SCRIPT_DIR / "targets"
    if not targets_dir.exists():
        return {}
    cutoff = time.time() - (window_hours * 3600)
    for stage2_file in targets_dir.glob("*/stage2_result.json"):
        try:
            if stage2_file.stat().st_mtime < cutoff:
                continue
        except OSError:
            continue
        try:
            data = json.loads(stage2_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if data.get("verdict") != "reject":
            continue
        rejection_codes = list(data.get("rejection_codes") or [])
        for code in rejection_codes:
            cat = _stage2_reject_category(str(code or ""))
            counts[cat] = counts.get(cat, 0) + 1
        if rejection_codes:
            continue
        for reason in data.get("rejection_reasons") or []:
            cat = _stage2_reject_category(str(reason or ""))
            counts[cat] = counts.get(cat, 0) + 1
    return {k: v for k, v in counts.items() if v >= min_count}


def _stage2_reject_category(reason: str) -> str:
    r = reason.lower()
    if r in {
        "bad_target_file",
        "line_cap",
        "empty_content",
        "compile_failed",
        "external_provenance_leak",
        "killo_review_reject",
    }:
        return r
    if "duplicate \\leanchecked" in r or "duplicate \\leantarget" in r:
        return "duplicate_lean_marker"
    if "build invariant" in r:
        return "build_invariant"
    if "content duplication" in r:
        return "content_duplication"
    if "non-latex" in r or "trailing" in r:
        return "non_latex_trailing"
    if "undefined control sequence" in r or "undefined macro" in r:
        return "undefined_macro"
    if (
        "800-line" in r
        or "line cap" in r
        or "far past the 800" in r
        or "would exceed" in r
        or "exceed 800 lines" in r
    ):
        return "line_cap"
    if (
        ("target" in r and "does not exist" in r)
        or "not a concrete body file" in r
    ):
        return "bad_target_file"
    if (
        "transport-style" in r
        or "without a transport-citation" in r
        or "without a transport citation" in r
        or "implicit transport step" in r
    ):
        return "implicit_transport_without_citation"
    if "implicit inversion" in r or "no labeled theorem/lemma" in r:
        return "missing_inversion_or_projection_lemma"
    if "display math" in r:
        return "latex_layout"
    if "operatorname" in r or "macro convention" in r:
        return "macro_convention"
    if "no theorem" in r or "no \\begin{theorem}" in r or "contains json" in r:
        return "missing_appendable_latex_environment"
    m = re.search(r"item\s*(\d+)", r)
    if m:
        return f"checklist_item_{m.group(1)}"
    return "other"


def stage2_reject_advice(clusters: dict[str, int]) -> str:
    cats = set(clusters)
    if cats and cats <= {"line_cap", "bad_target_file"}:
        return "consider splitting or rerouting target files"
    if cats and cats <= {"undefined_macro", "build_invariant"}:
        return "consider hardening compile-hygiene checks"
    if cats and cats <= {
        "implicit_transport_without_citation",
        "missing_inversion_or_projection_lemma",
    }:
        return "consider adding transport/inversion obligations before writeback"
    if cats and cats <= {
        "latex_layout",
        "missing_appendable_latex_environment",
        "macro_convention",
        "non_latex_trailing",
    }:
        return "consider hardening appendable-LaTeX prompt checks"
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

    Two-pool mode: pass codex_parallel + oracle_parallel.
      - codex pool runs codex_track at high concurrency (no tab dependency).
      - oracle pool drains `.oracle_pending` markers, capped at active tabs.
    Single-pool compatibility mode: pass `parallel` only (codex first, oracle
    fallback in the same worker, capped at tabs).

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


def git_sync_dev(*, timeout_seconds: int = DEFAULT_DEV_SYNC_TIMEOUT_SECONDS, label: str = "") -> bool:
    """Synchronize BEDC with the shared auto-dev integration branch.

    Sync is required so this branch does not duplicate work already produced
    by auto-dev/loning.  Safety lives in dev_sync_resolver's path protection,
    conflict handling, and post-merge gates, not in disabling sync.
    """
    proc = subprocess.Popen(
        ["python3", str(DEV_SYNC_RESOLVER)],
        cwd=str(REPO_ROOT),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass
        try:
            stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            stdout, stderr = "", ""
        suffix = f" ({label})" if label else ""
        supervisor_log(
            f"git_sync_dev{suffix}: timeout after {timeout_seconds}s; deferred to next supervisor tick"
        )
        return False
    output = (stdout or stderr or "").strip()
    summary = " ".join(output.split())[:500]
    suffix = f" ({label})" if label else ""
    if proc.returncode == 0:
        supervisor_log(f"git_sync_dev{suffix}: ok {summary}")
        return True
    supervisor_log(f"git_sync_dev{suffix}: blocked rc={proc.returncode} {summary}")
    return False


def trigger_probe(*, no_dev_sync: bool = False) -> None:
    if not no_dev_sync:
        git_sync_dev()
    supervisor_log("triggering auto_discovery probe")
    # Capture output so silent crashes (e.g. prompt format() KeyError) are
    # visible in the supervisor logs instead of vanishing into DEVNULL.
    log_path = SUPERVISOR_LOG_DIR / f"probe_{_now_tag_safe()}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["python3", str(AUTO_DISCOVERY), "probe", "--append"]
    if no_dev_sync:
        cmd.append("--no-dev-sync")
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
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
    cmd = ["python3", str(AUTO_DISCOVERY), "curriculum", "--append"]
    if no_dev_sync:
        cmd.append("--no-dev-sync")
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
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
    cmd = ["python3", str(AUTO_DISCOVERY), "paper_review", "--append"]
    if no_dev_sync:
        cmd.append("--no-dev-sync")
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def trigger_oracle_board_refill() -> None:
    """Ask oracle in the BEDC Project for new BOARD candidates.

    Complementary to auto_discovery probe: probe finds mechanical gaps via
    codex static scan, oracle_board_refill uses the Project's attached paper
    context plus research intuition to suggest deeper directions. Run when
    BOARD unfinished count is low and probe alone isn't refilling.
    """
    supervisor_log("triggering oracle_board_refill")
    run_id = _now_tag_safe()
    log_path = SUPERVISOR_LOG_DIR / f"refill_{run_id}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "python3",
        str(SCRIPT_DIR / "oracle_board_refill.py"),
        "--no-attach-pdf",
        "--run-id",
        run_id,
    ]
    status = server_status()
    if status.get("dispatch_ready_poll_agents"):
        supervisor_log(
            "oracle_board_refill: dispatch-ready tab present; "
            "ignoring stale refill circuit breaker for this run"
        )
        cmd.append("--ignore-refill-circuit-breaker")
    elif status.get("project_active_poll_agents"):
        supervisor_log(
            "oracle_board_refill: BEDC project tab polling but no "
            "conversation tab dispatch-ready; allowing queued refill"
        )
        cmd.append("--allow-queue-without-tabs")
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )


def trigger_research_lane_refinement() -> None:
    """Run local wide-in/strict-out candidate refinement.

    This is the non-oracle local research lane: first audit old/new supply
    through plain philosophy/plain math readings, then let research_candidate_lane
    append only ready packets through board_spawn's normal gates.  It never
    writes paper text directly.
    """
    supervisor_log("triggering plain_math_review + research_candidate_lane")
    run_id = _now_tag_safe()
    log_path = SUPERVISOR_LOG_DIR / f"research_lane_{run_id}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "python3",
        "-c",
        (
            "import subprocess, sys; "
            f"cmds = [[sys.executable, {str(PLAIN_MATH_REVIEW)!r}, '--limit', '80'], "
            f"[sys.executable, {str(RESEARCH_CANDIDATE_LANE)!r}, '--limit', '24', '--append']]; "
            "rc = 0\n"
            "for cmd in cmds:\n"
            "    print('+', ' '.join(cmd), flush=True)\n"
            "    p = subprocess.run(cmd)\n"
            "    rc = rc or p.returncode\n"
            "sys.exit(rc)\n"
        ),
    ]
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
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


def run_loning_assimilator() -> dict | None:
    """Summarize loning watch output into structured local pipeline signals."""
    try:
        proc = subprocess.run(
            ["python3", str(LONING_ASSIMILATOR)],
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            timeout=90,
        )
    except subprocess.TimeoutExpired:
        supervisor_log("loning_assimilator: timed out")
        return None
    except OSError as exc:
        supervisor_log(f"loning_assimilator: failed to launch: {exc}")
        return None
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "").strip()
        supervisor_log(f"loning_assimilator: rc={proc.returncode} {err[:300]}")
        return None
    try:
        data = json.loads(proc.stdout.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        supervisor_log(f"loning_assimilator: output not JSON: {(proc.stdout or '')[:300]}")
        return None
    supervisor_log(
        f"loning_assimilator: relevant={data.get('relevant_commits')} "
        f"signals={data.get('signal_counts') or {}}"
    )
    return data


def trigger_curator(*, no_dev_sync: bool = False) -> None:
    if not no_dev_sync:
        git_sync_dev()
    supervisor_log("triggering auto_discovery curator")
    cmd = ["python3", str(AUTO_DISCOVERY), "curator", "--append"]
    if no_dev_sync:
        cmd.append("--no-dev-sync")
    subprocess.Popen(
        cmd,
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


def current_branch_name() -> str:
    return _git(["branch", "--show-current"]).stdout.strip()


def current_head() -> str:
    return _git(["rev-parse", "HEAD"]).stdout.strip()


def current_upstream() -> str:
    return _git(["rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"]).stdout.strip()


def ahead_behind_upstream() -> tuple[int, int] | None:
    result = _git(["rev-list", "--left-right", "--count", "@{u}...HEAD"])
    if result.returncode != 0:
        return None
    parts = result.stdout.strip().split()
    if len(parts) != 2:
        return None
    try:
        behind = int(parts[0])
        ahead = int(parts[1])
    except ValueError:
        return None
    return ahead, behind


def merge_current_upstream_for_push(branch: str) -> bool:
    """Integrate the current branch's upstream before retrying a push.

    This handles the common non-fast-forward case where the bridge lane pushed
    a small commit to this same branch while the local supervisor accumulated
    paper-writeback commits. It only runs from clean post-commit states.
    """
    dirty = _git(["status", "--porcelain"]).stdout.strip()
    if dirty:
        supervisor_log("push-sync: skipped upstream merge because worktree is dirty")
        return False
    upstream = current_upstream()
    if not upstream:
        supervisor_log("push-sync: skipped upstream merge because upstream is unknown")
        return False
    fetch = _git(["fetch", "origin"], capture=False)
    if fetch.returncode != 0:
        supervisor_log(f"push-sync: fetch {branch} failed rc={fetch.returncode}")
        return False
    merge = _git(["merge", "--no-edit", upstream], capture=False)
    if merge.returncode == 0:
        supervisor_log(f"push-sync: merged {upstream} into {branch}")
        return True
    supervisor_log(f"push-sync: merge {upstream} failed rc={merge.returncode}; aborting merge")
    _git(["merge", "--abort"], capture=False)
    return False


def retry_pending_network_push() -> bool:
    """Resume a push that may have failed during a network outage.

    A resume is only valid for the exact HEAD recorded by the checkpoint.
    Without that guard, an old local merge can be pushed later after the branch
    has deliberately been moved back to a paper-native BEDC tip.
    """
    branch = current_branch_name()
    if not branch:
        return False
    checkpoint: dict = {}
    if NETWORK_RESUME_FILE.exists():
        try:
            loaded = json.loads(NETWORK_RESUME_FILE.read_text(encoding="utf-8"))
            if isinstance(loaded, dict):
                checkpoint = loaded
        except (OSError, json.JSONDecodeError):
            checkpoint = {}
    if not checkpoint:
        return False
    checkpoint_head = str(checkpoint.get("head") or "").strip()
    head = current_head()
    if checkpoint_head and checkpoint_head != head:
        supervisor_log(
            "network-resume: clearing stale checkpoint "
            f"head={checkpoint_head[:12]} current={head[:12]}"
        )
        _clear_network_resume_checkpoint()
        return False
    relation = ahead_behind_upstream()
    if relation is None:
        _write_network_resume_checkpoint(
            "upstream_unknown",
            branch,
            "could not resolve upstream while checking pending network resume",
            head=head,
        )
        supervisor_log("network-resume: upstream unknown; will retry next tick")
        return False
    ahead, behind = relation
    if ahead == 0:
        if NETWORK_RESUME_FILE.exists():
            supervisor_log("network-resume: upstream caught up; clearing checkpoint")
            _clear_network_resume_checkpoint()
        return False
    if behind:
        reason = (
            f"branch is ahead={ahead} and behind={behind}; "
            "sync resolver must integrate upstream before push"
        )
        _write_network_resume_checkpoint(
            "push_blocked_diverged",
            branch,
            reason,
            head=current_head(),
            upstream=current_upstream(),
        )
        supervisor_log(f"network-resume: {reason}")
        git_sync_dev()
        return False
    supervisor_log(f"network-resume: retrying push of {ahead} commit(s) on {branch}")
    push = _git(["push", "origin", branch], capture=False)
    if push.returncode != 0:
        _write_network_resume_checkpoint(
            "push_failed",
            branch,
            f"git push rc={push.returncode}",
            head=current_head(),
            upstream=current_upstream(),
        )
        supervisor_log(f"network-resume: push still failing rc={push.returncode}")
        return False
    _clear_network_resume_checkpoint()
    supervisor_log(f"network-resume: push complete on {branch}")
    return True


def commit_and_push_if_changed() -> bool:
    # Acquire paper_writes lock so we never commit a partial Stage 2 state
    # (where _append_to_tex has run but _make_paper hasn't decided
    # accept/rollback yet). Stage 2 holds this lock through append + make
    # + potential rollback, so commit only sees a consistent post-Stage-2
    # working tree.
    from locks import file_lock
    with file_lock("paper_writes"):
        pre_relation = ahead_behind_upstream()
        if pre_relation:
            pre_ahead, pre_behind = pre_relation
            if pre_behind:
                supervisor_log(
                    "auto-commit: branch behind upstream; running sync before commit "
                    f"(ahead={pre_ahead}, behind={pre_behind})"
                )
                git_sync_dev()
                pre_relation = ahead_behind_upstream()
                if pre_relation:
                    pre_ahead, pre_behind = pre_relation
            if pre_ahead or pre_behind:
                supervisor_log(
                    "auto-commit: skipped because branch is not aligned with upstream "
                    f"(ahead={pre_ahead}, behind={pre_behind})"
                )
                return False
        diff = _git([
            "status", "--porcelain",
            "papers/bedc/parts",
            "tools/bedc-deep/BOARD.md",
            "tools/bedc-deep/BOARD.completed.md",
        ])
        if not diff.stdout.strip():
            return False
        files: list[str] = []
        for line in diff.stdout.splitlines():
            parts = line.strip().split(None, 1)
            if len(parts) == 2:
                files.append(parts[1])
        if not files:
            return False
        local_only_state_files = {
            "tools/bedc-deep/BOARD.md",
            "tools/bedc-deep/BOARD.completed.md",
        }
        committable_files = [
            path for path in files
            if path not in local_only_state_files
        ]
        if not committable_files:
            supervisor_log(
                "auto-commit: skipped push for local-only BOARD state files"
            )
            return False
        skipped = len(files) - len(committable_files)
        if skipped:
            supervisor_log(
                f"auto-commit: {len(committable_files)} committable changed files "
                f"({skipped} local-only BOARD state file(s) skipped)"
            )
        else:
            supervisor_log(f"auto-commit: {len(committable_files)} changed files")
        _git(["add", *committable_files], capture=False)
        msg = f"bedc-deep supervisor: paper writeback batch {_now_iso()}"
        rc = _git(["commit", "-m", msg]).returncode
        if rc != 0:
            supervisor_log("auto-commit: git commit returned non-zero (race or empty)")
            return False
        branch = current_branch_name()
        relation = ahead_behind_upstream()
        if relation:
            ahead, behind = relation
            if behind:
                reason = (
                    f"branch behind upstream by {behind}; "
                    "sync resolver must integrate upstream before push"
                )
                supervisor_log(f"auto-commit: {reason}")
                git_sync_dev()
                _write_network_resume_checkpoint(
                    "push_blocked_diverged",
                    branch,
                    reason,
                    head=current_head(),
                    upstream=current_upstream(),
                )
                return False
        push = _git(["push", "origin", branch], capture=False)
        if push.returncode != 0:
            supervisor_log(f"auto-commit: push failed rc={push.returncode}")
            _write_network_resume_checkpoint(
                "push_failed_after_commit",
                branch,
                f"git push rc={push.returncode}",
                head=current_head(),
                upstream=current_upstream(),
            )
            return False
    supervisor_log(f"auto-commit + push complete on {branch}")
    _clear_network_resume_checkpoint()
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
    import importlib
    import pi_agent_v1 as pi_module
    pi_module = importlib.reload(pi_module)

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
        if "allow_oracle_candidate_generation" in args:
            supervisor_state["allow_oracle_candidate_generation"] = bool(args["allow_oracle_candidate_generation"])
            applied.append(
                "oracle_candidate_generation="
                f"{'on' if supervisor_state['allow_oracle_candidate_generation'] else 'off'}"
            )
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
                        help="Single-pool compatibility mode used only when both two-pool sizes are set to 0.")
    parser.add_argument("--codex-parallel", type=int, default=DEFAULT_CODEX_PARALLEL,
                        help="Two-pool mode: codex_track workers (compute-bound, no tab dep). Recommended 6-8.")
    parser.add_argument("--oracle-parallel", type=int, default=DEFAULT_ORACLE_PARALLEL,
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
                        help="Cooldown between oracle_board_refill runs when --allow-oracle-candidate-generation "
                             "is set. Default supervisor operation skips oracle BOARD refill and keeps "
                             "Codex, bridge, and deterministic local lanes primary.")
    parser.add_argument("--research-lane-cooldown-hours", type=float, default=DEFAULT_RESEARCH_LANE_COOLDOWN_HOURS,
                        help="Cooldown between local plain-review + research-candidate refinement runs. "
                             "This wide-in/strict-out lane does not write paper text directly.")
    parser.add_argument("--oracle-refill-research-grace-minutes", type=float,
                        default=DEFAULT_ORACLE_REFILL_RESEARCH_GRACE_MINUTES,
                        help="When BOARD is low-water, defer oracle_board_refill for this many minutes after "
                             "a local research-lane run if the candidate inbox still has refinement backlog. "
                             "This keeps the pipeline reasoning over existing candidates before requesting more.")
    parser.add_argument("--allow-oracle-candidate-generation", action="store_true",
                        default=DEFAULT_ALLOW_ORACLE_CANDIDATE_GENERATION,
                        help="Opt in to oracle_board_refill as a BOARD candidate generator. Default off so "
                             "Codex, bridge, and deterministic local lanes remain the routine BOARD supply; "
                             "oracle workers still drain explicit escalation tasks.")
    parser.add_argument("--dev-sync-cooldown-minutes", type=float, default=DEFAULT_DEV_SYNC_COOLDOWN_MINUTES,
                        help="Cooldown between BEDC sync attempts from origin/auto-dev through dev_sync_resolver.")
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
    parser.add_argument("--dev-sync", action="store_true",
                        default=DEFAULT_DEV_SYNC_ENABLED,
                        help="Enable BEDC sync from origin/auto-dev. Default on so the BEDC branch stays joined to the shared integration trunk.")
    parser.add_argument("--no-dev-sync", action="store_true",
                        help="Disable BEDC sync from origin/auto-dev.")
    parser.add_argument("--status-once", action="store_true",
                        help="Print a local JSON status snapshot and exit without starting networked workers.")
    parser.add_argument("--allow-lean-adjacent-discovery", action="store_true",
                        default=DEFAULT_ALLOW_LEAN_ADJACENT_DISCOVERY,
                        help="Opt in to legacy auto_discovery probe/curriculum/curator triggers. "
                             "Default off so the always-on BEDC supervisor remains paper-native.")
    parser.add_argument("--inner-restart-backoff", type=int, default=DEFAULT_INNER_RESTART_BACKOFF_S)
    args = parser.parse_args()

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    if args.status_once:
        print(json.dumps(supervisor_status_snapshot(), indent=2, ensure_ascii=False))
        return 0
    if STOP_FILE.exists():
        supervisor_log(f"STOP_FILE present; supervisor not starting: {STOP_FILE}")
        return 0
    if not assert_required_branch():
        return 2

    dev_sync_enabled = bool(args.dev_sync) and not bool(args.no_dev_sync)
    no_dev_sync = not dev_sync_enabled

    supervisor_log(
        f"supervisor starting (parallel={args.parallel}, "
        f"claude_review={'off' if args.no_claude_review else 'on'}, "
        f"auto_commit={'off' if args.no_auto_commit else 'on'}, "
        f"dev_sync={'on' if dev_sync_enabled else 'off'}, "
        f"lean_adjacent_discovery={'on' if args.allow_lean_adjacent_discovery else 'off'}, "
        f"oracle_candidate_generation={'on' if args.allow_oracle_candidate_generation else 'off'})"
    )

    if dev_sync_enabled:
        try:
            git_sync_dev(timeout_seconds=STARTUP_DEV_SYNC_TIMEOUT_SECONDS, label="startup")
        except Exception as exc:
            supervisor_log(f"git_sync_dev startup error: {exc}")

    last_probe_ts = 0.0
    last_curriculum_ts = 0.0
    last_curator_ts = 0.0
    last_claude_review_ts = 0.0
    last_oracle_refill_ts = 0.0
    last_research_lane_ts = 0.0
    last_paper_review_ts = 0.0
    last_loning_watch_ts = 0.0
    last_dev_sync_ts = 0.0
    last_completed_count = board_completed_count()
    last_tab_alert_ts = 0.0
    last_zero_extract_alert_ts = 0.0
    last_candidate_inbox_alert_ts = 0.0
    inner: subprocess.Popen | None = None

    supervisor_state: dict = {
        "inner": None,
        "probe_cooldown_hours": args.probe_cooldown_hours,
        "curriculum_cooldown_hours": args.curriculum_cooldown_hours,
        "paper_review_cooldown_hours": args.paper_review_cooldown_hours,
        "curator_cooldown_hours": args.curator_cooldown_hours,
        "pi_cooldown_hours": args.claude_review_hours,
        "oracle_refill_cooldown_hours": args.oracle_refill_cooldown_hours,
        "research_lane_cooldown_hours": args.research_lane_cooldown_hours,
        "oracle_refill_research_grace_minutes": args.oracle_refill_research_grace_minutes,
        "pipeline_version": args.pipeline_version,
        "attach_pdf": args.attach_pdf,
        "allow_lean_adjacent_discovery": args.allow_lean_adjacent_discovery,
        "allow_oracle_candidate_generation": args.allow_oracle_candidate_generation,
    }

    try:
        while not STOP_FILE.exists():
            if not assert_required_branch():
                break
            ensure_server()

            if dev_sync_enabled and (_now() - last_dev_sync_ts) / 60.0 >= args.dev_sync_cooldown_minutes:
                git_sync_dev()
                last_dev_sync_ts = _now()

            cleaned = stale_cleanup()
            if cleaned:
                supervisor_log(f"cleaned {cleaned} stale claims")

            archived = board_archive_completed()
            if archived:
                supervisor_log(f"archived {archived} completed BOARD entries")

            retried = crash_retry_sweep()
            if retried:
                supervisor_log(f"reset {retried} crashed targets for retry")

            unfinished = board_unfinished_count()
            inner = supervisor_state.get("inner")
            if unfinished > 0 and (inner is None or inner.poll() is not None):
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
            elif unfinished == 0 and inner is not None and inner.poll() is not None:
                supervisor_log("inner exited and BOARD has no unfinished targets; waiting for refill")
                supervisor_state["inner"] = None

            since_probe_h = (_now() - last_probe_ts) / 3600.0
            since_curriculum_h = (_now() - last_curriculum_ts) / 3600.0
            since_oracle_refill_h = (_now() - last_oracle_refill_ts) / 3600.0
            since_research_lane_h = (_now() - last_research_lane_ts) / 3600.0
            since_paper_review_h = (_now() - last_paper_review_ts) / 3600.0
            inbox_health = candidate_inbox_health()
            research_lane_triggered = False
            allow_lean_adjacent_discovery = bool(
                supervisor_state.get("allow_lean_adjacent_discovery", False)
            )
            if unfinished < args.low_water and since_probe_h > supervisor_state["probe_cooldown_hours"]:
                if allow_lean_adjacent_discovery:
                    supervisor_log(f"BOARD low water (unfinished={unfinished}) → probe")
                    trigger_probe(no_dev_sync=no_dev_sync)
                else:
                    supervisor_log(
                        "BOARD low water: skipped auto_discovery probe "
                        "because paper-native supervisor defaults forbid "
                        "Lean-adjacent discovery; paper_review, research_lane, "
                        "and bridge/local intake remain enabled"
                    )
                last_probe_ts = _now()
            if unfinished < args.low_water and since_curriculum_h > supervisor_state["curriculum_cooldown_hours"]:
                if allow_lean_adjacent_discovery:
                    supervisor_log(f"BOARD low water (unfinished={unfinished}) → curriculum probe")
                    trigger_curriculum_probe(no_dev_sync=no_dev_sync)
                else:
                    supervisor_log(
                        "BOARD low water: skipped curriculum probe because "
                        "paper-native supervisor defaults forbid Lean-adjacent "
                        "discovery"
                    )
                last_curriculum_ts = _now()
            if unfinished < args.low_water and since_research_lane_h > supervisor_state["research_lane_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → research_lane_refinement")
                trigger_research_lane_refinement()
                last_research_lane_ts = _now()
                research_lane_triggered = True
            if unfinished < args.low_water and since_paper_review_h > supervisor_state["paper_review_cooldown_hours"]:
                supervisor_log(f"BOARD low water (unfinished={unfinished}) → paper_review")
                trigger_paper_review(no_dev_sync=no_dev_sync)
                last_paper_review_ts = _now()
            if unfinished < args.low_water and since_oracle_refill_h > supervisor_state["oracle_refill_cooldown_hours"]:
                allow_oracle_candidate_generation = bool(
                    supervisor_state.get("allow_oracle_candidate_generation", False)
                )
                if not allow_oracle_candidate_generation:
                    supervisor_log(
                        f"BOARD low water (unfinished={unfinished}) → skipped oracle_board_refill; "
                        "oracle candidate generation is disabled by default, while "
                        "Codex, bridge, and deterministic local lanes remain primary"
                    )
                    last_oracle_refill_ts = _now()
                else:
                    grace_minutes = float(supervisor_state.get("oracle_refill_research_grace_minutes", args.oracle_refill_research_grace_minutes))
                    since_research_lane_m = (_now() - last_research_lane_ts) / 60.0 if last_research_lane_ts else 999999.0
                    defer_refill, defer_reason = should_defer_oracle_refill_for_research(
                        research_lane_triggered=research_lane_triggered,
                        inbox_health=inbox_health,
                        since_research_lane_m=since_research_lane_m,
                        grace_minutes=grace_minutes,
                    )
                    if defer_refill and defer_reason == "local_research_lane_triggered":
                        supervisor_log(
                            f"BOARD low water (unfinished={unfinished}) → deferred oracle_board_refill; "
                            "local research lane triggered first"
                        )
                    elif defer_refill:
                        supervisor_log(
                            f"BOARD low water (unfinished={unfinished}) → deferred oracle_board_refill; "
                            f"candidate refinement backlog present; local lanes must drain/refine it before oracle refill "
                            f"(research_lane ran {since_research_lane_m:.1f}m ago; legacy grace={grace_minutes:.1f}m)"
                        )
                    else:
                        if defer_reason == "material_refinement_backlog_grace_elapsed":
                            supervisor_log(
                                f"BOARD low water (unfinished={unfinished}) → oracle_board_refill; "
                                f"candidate refinement grace elapsed "
                                f"(research_lane ran {since_research_lane_m:.1f}m ago; grace={grace_minutes:.1f}m)"
                            )
                        elif defer_reason == "no_material_refinement_backlog":
                            supervisor_log(
                                f"BOARD low water (unfinished={unfinished}) → oracle_board_refill; "
                                "no material candidate refinement backlog"
                            )
                        else:
                            supervisor_log(f"BOARD low water (unfinished={unfinished}) → oracle_board_refill")
                        trigger_oracle_board_refill()
                        last_oracle_refill_ts = _now()

            done_now = board_completed_count()
            since_curator_h = (_now() - last_curator_ts) / 3600.0
            if done_now - last_completed_count >= COMPLETIONS_PER_CURATOR and since_curator_h > supervisor_state["curator_cooldown_hours"]:
                if allow_lean_adjacent_discovery:
                    supervisor_log(f"completions delta={done_now - last_completed_count} → curator")
                    trigger_curator(no_dev_sync=no_dev_sync)
                else:
                    supervisor_log(
                        f"completions delta={done_now - last_completed_count}: "
                        "skipped curator because paper-native supervisor "
                        "defaults forbid Lean-adjacent discovery"
                    )
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

            oracle_health = server_status()
            zero_extract_details = zero_extraction_hang_details(oracle_health)
            if zero_extract_details and _now() - last_zero_extract_alert_ts > ZERO_EXTRACTION_ALERT_COOLDOWN_S:
                agents_csv = ",".join(d.get("agent_id", "?") for d in zero_extract_details)
                url_tails = ",".join(
                    d.get("url_tail", "") for d in zero_extract_details if d.get("url_tail")
                )
                supervisor_log(
                    "oracle health: zero-extraction hang "
                    f"agents={agents_csv} "
                    f"url_tails={url_tails or '?'}; refresh affected tab(s) only"
                )
                notify_tail = f" URL tail: {url_tails}" if url_tails else ""
                macos_notify(
                    "BEDC supervisor: oracle zero extraction",
                    f"{agents_csv} has an active task but extracted 0 chars; refresh only the affected ChatGPT tab.{notify_tail}",
                )
                last_zero_extract_alert_ts = _now()

            latest_age = inbox_health.get("latest_event_age_seconds")
            try:
                latest_age_s = int(latest_age)
            except (TypeError, ValueError):
                latest_age_s = 0
            if (
                unfinished < args.low_water
                and latest_age_s >= CANDIDATE_INBOX_STALE_SECONDS
                and _now() - last_candidate_inbox_alert_ts > CANDIDATE_INBOX_ALERT_COOLDOWN_S
            ):
                latest = inbox_health.get("latest_event") or {}
                supervisor_log(
                    "candidate inbox: no recent intake "
                    f"latest_age_s={latest_age_s} "
                    f"latest_event={latest.get('event') or '?'} "
                    f"source={latest.get('source') or '?'} "
                    f"source_ages={candidate_inbox_source_age_summary(inbox_health) or '?'} "
                    f"title={str(latest.get('title') or '')[:80]!r}"
                )
                last_candidate_inbox_alert_ts = _now()

            clusters = stage2_reject_clusters()
            if clusters:
                supervisor_log(f"stage2 reject clusters: {clusters} — {stage2_reject_advice(clusters)}")

            if not args.no_loning_watch:
                since_loning_watch_m = (_now() - last_loning_watch_ts) / 60.0
                if since_loning_watch_m > args.loning_watch_minutes:
                    run_loning_watch()
                    run_loning_assimilator()
                    last_loning_watch_ts = _now()

            if not args.no_auto_commit:
                try:
                    retry_pending_network_push()
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
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

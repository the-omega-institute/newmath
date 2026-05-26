#!/usr/bin/env python3
"""Single-screen status view for the BEDC bedc-deep pipeline.

Prints to stdout: server status, BOARD breakdown, target lifecycle table,
failure_kind histogram, Stage 2 reject clusters, recent commits, supervisor
log tail. Runs read-only — no state mutation.

Refresh repeatedly with `watch -n 30 python3 tools/bedc-deep/dashboard.py`
or just rerun manually.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "state"
TARGETS_DIR = SCRIPT_DIR / "targets"
SUPERVISOR_LOG = STATE_DIR / "supervisor_logs" / "supervisor.log"
SUPERVISOR_LOG_DIR = STATE_DIR / "supervisor_logs"
BOARD_REFILL_LOG_DIR = STATE_DIR / "board_refill_logs"
DISCOVERY_LOG_DIR = STATE_DIR / "discovery_logs"
BOARD_SPAWN_LATEST = STATE_DIR / "board_spawn_latest.json"
RESEARCH_CANDIDATES_LATEST = STATE_DIR / "research_candidates_latest.md"
RESEARCH_BOARD_SPAWN_LATEST = STATE_DIR / "research_board_spawn_latest.json"
PI_RECENT_CYCLES = STATE_DIR / "pi_recent_cycles.jsonl"
LONING_ASSIMILATION_JOURNAL = STATE_DIR / "loning_assimilation.jsonl"
LONING_WATCH_JOURNAL = STATE_DIR / "loning_watch.jsonl"
ORACLE_SERVER_URL = "http://localhost:8767"
PI_DRY_BOARD_SUPPRESSION_COMMIT = "cc71b590f8"

sys.path.insert(0, str(SCRIPT_DIR))


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _parse_iso(value: object) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        ts = datetime.fromisoformat(text)
    except ValueError:
        return None
    if ts.tzinfo is None:
        return ts.replace(tzinfo=timezone.utc)
    return ts.astimezone(timezone.utc)


def _safe_get_server() -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=3) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception as exc:
        return {"_error": str(exc), "_error_type": type(exc).__name__}


def _git(args: list[str]) -> str:
    try:
        return subprocess.run(
            ["git", *args],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        ).stdout
    except Exception:
        return ""


def _git_commit_ts(commit: str) -> datetime | None:
    out = _git(["show", "-s", "--format=%cI", commit]).strip()
    return _parse_iso(out)


def _section(title: str) -> str:
    bar = "─" * (len(title) + 4)
    return f"\n┌{bar}┐\n│  {title}  │\n└{bar}┘"


def _fmt_age(seconds: object) -> str:
    try:
        total = int(seconds)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return "?"
    if total < 60:
        return f"{total}s"
    minutes = total // 60
    if minutes < 60:
        return f"{minutes}m"
    hours = minutes // 60
    if hours < 48:
        return f"{hours}h{minutes % 60:02d}m"
    days = hours // 24
    return f"{days}d{hours % 24:02d}h"


def _zero_extraction_url_tails(s: dict) -> list[str]:
    tails: list[str] = []
    recent = s.get("recent_agents") or {}
    for agent_id in s.get("zero_extraction_hang_agents") or []:
        rec = recent.get(str(agent_id)) or {}
        metrics = rec.get("metrics") or {}
        tail = str(metrics.get("url_tail") or "").strip()
        if tail:
            tails.append(tail)
    return tails


def render_server(s: dict) -> str:
    if "_error" in s:
        err = str(s["_error"])
        if "Operation not permitted" in err:
            return (
                "  status: UNAVAILABLE (local sandbox denied localhost status check)\n"
                "  hint: run `python3 tools/bedc-deep/oracle_client.py --status` "
                "for authoritative oracle health"
            )
        return f"  status: DOWN ({s['_error']})"
    diag = s.get("diagnosis", "?")
    busy = s.get("agents_busy", "?")
    cap = s.get("max_agents", "?")
    queue = s.get("queue_length", "?")
    completed = s.get("completed", "?")
    active_recent = len(s.get("active_recent_agents") or [])
    dispatch_ready = len(s.get("dispatch_ready_poll_agents") or [])
    out = [
        f"  diagnosis: {diag}",
        f"  agents:    {busy}/{cap} busy   queue={queue}   completed={completed}",
        f"  recent agents (last 120s): {active_recent}   dispatch-ready: {dispatch_ready}",
    ]
    if s.get("dispatch_ready_poll_agents"):
        out.append(
            "  dispatch-ready tabs: "
            + ", ".join(map(str, s.get("dispatch_ready_poll_agents") or []))
        )
    elif s.get("project_active_poll_agents"):
        out.append(
            "  project-active tabs are not dispatch-ready until they are on /c/... conversation pages"
        )
    for k, v in (s.get("agents") or {}).items():
        out.append(f"    busy {k}: task={v.get('task_id','?')} elapsed={v.get('elapsed','?')}s")
    if s.get("zero_extraction_hang_agents"):
        agents = ",".join(map(str, s.get("zero_extraction_hang_agents") or []))
        seconds = s.get("zero_extraction_hang_seconds", "?")
        out.append(f"  zero-extraction hang: {agents} >= {seconds}s with 0 extracted chars")
    url_tails = _zero_extraction_url_tails(s)
    if url_tails:
        out.append(f"  affected URL tail(s): {', '.join(url_tails)}")
    return "\n".join(out)


def render_board() -> str:
    from dispatch_bedc_target import parse_board
    import board_archive
    targets = parse_board()
    active_total = len(targets)
    archived_completed = len(board_archive.parse_board_file(board_archive.COMPLETED_BOARD_PATH))
    finished = 0
    in_progress = 0
    pending = 0
    for t in targets.values():
        if (STATE_DIR / f"{t.slug}.json").exists():
            finished += 1
        elif (STATE_DIR / t.slug / ".in_progress").exists():
            in_progress += 1
        else:
            pending += 1
    finished_total = finished + archived_completed
    out = [
        (
            f"  active: {active_total}   finished: {finished_total} "
            f"(archived={archived_completed})   in_progress: {in_progress}   pending: {pending}"
        ),
    ]
    return "\n".join(out)


def render_active_board_targets(limit: int = 12) -> str:
    from dispatch_bedc_target import parse_board

    targets = parse_board()
    rows: list[dict[str, object]] = []
    now = datetime.now(timezone.utc)
    for target in targets.values():
        done_path = STATE_DIR / f"{target.slug}.json"
        if done_path.exists():
            continue
        marker = STATE_DIR / target.slug / ".in_progress"
        if marker.exists():
            status = "in_progress"
            try:
                age_seconds: object = now.timestamp() - marker.stat().st_mtime
            except OSError:
                age_seconds = None
        else:
            status = "pending"
            age_seconds = None
        rows.append({
            "target_id": target.target_id,
            "status": status,
            "age": _fmt_age(age_seconds) if age_seconds is not None else "-",
            "slug": target.slug,
            "title": target.title[:60],
        })
    if not rows:
        return "  (no active BOARD targets)"

    rows.sort(key=lambda item: (item["status"] != "in_progress", str(item["target_id"])))
    shown = rows if limit <= 0 else rows[:limit]
    lines = [f"  {'TARGET':<8} {'STATUS':<12} {'AGE':<8} TITLE"]
    for item in shown:
        lines.append(
            f"  {item['target_id']:<8} {item['status']:<12} {item['age']:<8} "
            f"{item['title']}  [{item['slug']}]"
        )
    if limit > 0 and len(rows) > len(shown):
        lines.append(f"  ... {len(rows) - len(shown)} more active rows omitted")
    return "\n".join(lines)


def _render_candidate_stats(data: dict, *, label: str) -> list[str]:
    by_event = data.get("by_event") or {}
    if not by_event:
        lines = [f"  {label}: events=0 sampled={data.get('sampled', 0)}"]
    else:
        parts = [f"{k}={v}" for k, v in by_event.items()]
        lines = [
            (
                f"  {label}: events={data.get('windowed', data.get('sampled', 0))} "
                f"sampled={data.get('sampled', 0)}   " + "   ".join(parts)
            )
        ]
    if data.get("latest_event_ts"):
        latest = data.get("latest_event") or {}
        title = str(latest.get("title") or "")[:48]
        lines.append(
            (
                f"  {label} latest: {_fmt_age(data.get('latest_event_age_seconds'))} ago "
                f"{latest.get('event') or '?'} from {latest.get('source') or '?'}"
                + (f" — {title}" if title else "")
            )
        )
    latest_by_source = data.get("latest_by_source") or {}
    if latest_by_source:
        recent_sources = sorted(
            latest_by_source.items(),
            key=lambda kv: int((kv[1] or {}).get("age_seconds") or 10**12),
        )[:5]
        parts = []
        for source, rec in recent_sources:
            parts.append(
                f"{source}:{_fmt_age((rec or {}).get('age_seconds'))} "
                f"{(rec or {}).get('event') or '?'}"
            )
        lines.append(f"  {label} latest by source: " + ", ".join(parts))
    rejection_reasons = data.get("rejection_reasons") or []
    if rejection_reasons:
        top = ", ".join(f"{r.get('reason')}={r.get('count')}" for r in rejection_reasons[:5])
        lines.append(f"  {label} top rejects: {top}")
    rejection_sources = data.get("rejection_sources") or []
    if rejection_sources:
        top = ", ".join(f"{r.get('reason')}={r.get('count')}" for r in rejection_sources[:5])
        lines.append(f"  {label} reject sources: {top}")
    logic_reasons = data.get("logic_packet_gate_reasons") or []
    if logic_reasons:
        top = ", ".join(f"{r.get('reason')}={r.get('count')}" for r in logic_reasons[:5])
        lines.append(f"  {label} logic gate rejects: {top}")
    current_logic_reasons = data.get("current_logic_packet_gate_reasons") or []
    stale_logic_rejections = int(data.get("stale_logic_packet_gate_rejections") or 0)
    if current_logic_reasons:
        top = ", ".join(
            f"{r.get('reason')}={r.get('count')}" for r in current_logic_reasons[:5]
        )
        suffix = f"; stale={stale_logic_rejections}" if stale_logic_rejections else ""
        lines.append(f"  {label} current logic gate rejects: {top}{suffix}")
    elif stale_logic_rejections:
        lines.append(f"  {label} current logic gate rejects: none; stale={stale_logic_rejections}")
    current_axis_reasons = data.get("current_forbidden_axis_reasons") or []
    stale_axis_rejections = int(data.get("stale_forbidden_axis_rejections") or 0)
    if current_axis_reasons:
        top = ", ".join(
            f"{r.get('reason')}={r.get('count')}" for r in current_axis_reasons[:5]
        )
        suffix = f"; stale={stale_axis_rejections}" if stale_axis_rejections else ""
        lines.append(f"  {label} current forbidden-axis rejects: {top}{suffix}")
    elif stale_axis_rejections:
        lines.append(
            f"  {label} current forbidden-axis rejects: none; stale={stale_axis_rejections}"
        )
    return lines


def render_candidate_inbox() -> str:
    try:
        import candidate_inbox
        data = candidate_inbox.stats()
        recent = candidate_inbox.stats(since_hours=6)
    except Exception as exc:
        return f"  unavailable: {exc}"
    lines = _render_candidate_stats(data, label="all")
    lines.extend(_render_candidate_stats(recent, label="last 6h"))
    return "\n".join(lines)


def _refill_stem(path: Path) -> str:
    name = path.name
    for suffix in (".prompt.txt", ".response.md", ".summary.json", ".log"):
        if name.endswith(suffix):
            return name[: -len(suffix)]
    return path.stem


def _refill_stem_time(stem: object) -> datetime | None:
    text = str(stem or "")
    match = re.fullmatch(r"refill_(\d{8})_(\d{6})", text)
    if not match:
        return None
    try:
        return datetime.strptime("".join(match.groups()), "%Y%m%d%H%M%S").replace(
            tzinfo=timezone.utc,
        )
    except ValueError:
        return None


def _read_text_prefix(path: Path, *, max_chars: int = 2000) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    if len(text) <= max_chars:
        return text
    return text[-max_chars:]


def _response_failure_kind(text: str) -> str:
    low = (text or "").strip().lower()
    if low.startswith("error: response too short or empty"):
        return "oracle_transport_empty_response"
    if low.startswith("error: duplicate response"):
        return "oracle_transport_duplicate_response"
    if low.startswith("error:"):
        return "oracle_transport_error_response"
    if not low:
        return "empty_response"
    return "unparseable_or_unclassified_response"


def _refill_wait_seconds(rec: dict) -> int | None:
    log_path = rec.get("log")
    if not isinstance(log_path, Path) or not log_path.exists():
        return None
    text = _read_text_prefix(log_path, max_chars=12000)
    submitted = list(re.finditer(r"\[board_refill\] submitted task=", text))
    if submitted:
        text = text[submitted[-1].start():]
    matches = re.findall(r"waiting\.\.\.\s+(\d+)s elapsed", text)
    if not matches:
        return None
    try:
        return max(int(item) for item in matches)
    except ValueError:
        return None


def _refill_prompt_note(rec: dict) -> str:
    prompt_path = rec.get("prompt")
    if not isinstance(prompt_path, Path) or not prompt_path.exists():
        return ""
    try:
        size = prompt_path.stat().st_size
    except OSError:
        return ""
    if size >= 1024:
        return f" prompt={size / 1024:.0f}k"
    return f" prompt={size}b"


def _next_refill_prompt_note() -> str:
    try:
        import oracle_board_refill

        if oracle_board_refill.refill_circuit_breaker_active():
            limit = getattr(oracle_board_refill, "DEFAULT_LOCAL_GAP_FALLBACK_LIMIT", 3)
            return (
                "  next refill path: local gap fallback "
                f"(oracle ultra transport circuit breaker active; limit={limit})"
            )
        ultra_refill = oracle_board_refill.should_use_ultra_refill()
        micro_refill = ultra_refill or oracle_board_refill.should_use_micro_refill()
        size = len(
            oracle_board_refill.build_refill_prompt(
                micro_refill=micro_refill,
                ultra_refill=ultra_refill,
            ).encode("utf-8")
        )
    except Exception as exc:
        return f"  next prompt estimate: unavailable ({type(exc).__name__})"
    mode = " ultra" if ultra_refill else " micro" if micro_refill else ""
    if size >= 1024:
        return f"  next prompt estimate:{mode} {size / 1024:.0f}k"
    return f"  next prompt estimate:{mode} {size}b"


def _board_active_count() -> int:
    try:
        from dispatch_bedc_target import parse_board

        return len(parse_board())
    except Exception:
        return -1


def _classify_board_judge_error(error: str) -> str:
    """Infer the stable BOARD judge outage kind from legacy summary errors."""
    low = (error or "").lower()
    if not low:
        return ""

    claude_kind = "claude_unavailable"
    if "organization does not have access to claude" in low:
        claude_kind = "claude_access_denied"
    elif "not logged in" in low or "please login again" in low:
        claude_kind = "claude_not_logged_in"
    elif "claude cli not found" in low:
        claude_kind = "claude_cli_missing"
    elif "claude disabled" in low:
        claude_kind = "claude_disabled"
    elif "claude judge rc=-9" in low or "timed out" in low:
        claude_kind = "claude_timeout"
    elif "claude judge output was not json" in low:
        claude_kind = "claude_non_json"

    codex_kind = ""
    if "codex fallback" in low:
        codex_kind = "codex_fallback_failed"
        if "failed to initialize in-process app-server client" in low:
            codex_kind = "codex_sandbox_init_failed"
        elif "operation not permitted" in low:
            codex_kind = "codex_operation_not_permitted"
        elif "output was not json" in low:
            codex_kind = "codex_non_json"

    if "claude judge" in low or "claude returned" in low or "claude " in low:
        if codex_kind:
            return f"board_judge_unavailable:{claude_kind}+{codex_kind}"
        return f"board_judge_unavailable:{claude_kind}"
    if codex_kind:
        return f"board_judge_unavailable:{codex_kind}"
    return ""


def _board_judge_action_lines(error_kind: str, *, prefix: str = "  ") -> list[str]:
    """Render operator guidance for shared BOARD judge outages."""
    if "board_judge_unavailable" not in error_kind:
        return []
    lines = [
        (
            f"{prefix}alert: shared BOARD judge/fallback is unavailable; "
            "do not bypass board_spawn, and do not refresh BEDC oracle tabs for this."
        )
    ]
    if "claude_not_logged_in" in error_kind:
        lines.append(
            f"{prefix}action: restore Claude CLI auth for the shared BOARD judge; "
            "this is separate from BEDC oracle browser tabs."
        )
    elif "claude_access_denied" in error_kind:
        lines.append(
            f"{prefix}action: restore Claude CLI organization access for the shared BOARD judge; "
            "this is separate from BEDC oracle browser tabs."
        )
    elif "claude_cli_missing" in error_kind:
        lines.append(
            f"{prefix}action: install or expose the Claude CLI used by board_spawn."
        )
    if "codex_sandbox_init_failed" in error_kind:
        lines.append(
            f"{prefix}note: Codex fallback also failed during sandbox app-server initialization."
        )
    elif "codex_operation_not_permitted" in error_kind:
        lines.append(
            f"{prefix}note: Codex fallback also hit an operation-permitted sandbox failure."
        )
    return lines


def _planner_action_lines(error_kind: str, *, prefix: str = "  ") -> list[str]:
    """Render operator guidance for PI planner/fallback outages."""
    if "planner_unavailable" not in error_kind:
        return []
    lines = [
        (
            f"{prefix}alert: PI planner/fallback is unavailable; "
            "this is a CLI-side planning issue, not a BEDC oracle tab-refresh signal."
        )
    ]
    if "claude_not_logged_in" in error_kind:
        lines.append(
            f"{prefix}action: restore Claude CLI auth for PI planning and shared judge paths."
        )
    elif "claude_access_denied" in error_kind:
        lines.append(
            f"{prefix}action: restore Claude CLI organization access for PI planning."
        )
    if "codex_sandbox_init_failed" in error_kind:
        lines.append(
            f"{prefix}note: Codex planner fallback also failed during sandbox app-server initialization."
        )
    elif "codex_operation_not_permitted" in error_kind:
        lines.append(
            f"{prefix}note: Codex planner fallback also hit an operation-permitted sandbox failure."
        )
    return lines


def _infer_refill_status(rec: dict) -> str:
    summary_path = rec.get("summary")
    if isinstance(summary_path, Path) and summary_path.exists():
        try:
            summary = json.loads(summary_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return "summary_unreadable"
        if summary.get("fallback") == "local_gap_scanner":
            accepted = summary.get("accepted", 0)
            proposed = summary.get("candidates_proposed", 0)
            error = str(summary.get("error") or "").strip()
            reject_suffix = _format_refill_reject_suffix(summary)
            error_kind = (
                str(summary.get("error_kind") or "").strip()
                or _classify_board_judge_error(error)
            )
            if summary.get("ok"):
                return (
                    f"local_gap_fallback accepted={accepted} proposed={proposed}"
                    f"{reject_suffix}"
                )
            if error_kind.startswith("board_judge_unavailable"):
                return (
                    "local_gap_fallback_judge_unavailable "
                    f"accepted={accepted} proposed={proposed} kind={error_kind}"
                )
            if "claude judge" in error.lower() or "codex fallback" in error.lower():
                return (
                    "local_gap_fallback_judge_unavailable "
                    f"accepted={accepted} proposed={proposed}"
                )
            return (
                "local_gap_fallback_failed "
                f"accepted={accepted} proposed={proposed}"
                f"{reject_suffix}"
                + (f" error={error[:80]}" if error else "")
            )
        if summary.get("ok"):
            accepted = summary.get("accepted", 0)
            proposed = summary.get("candidates_proposed", 0)
            return f"ok accepted={accepted} proposed={proposed}"
        error = str(summary.get("error") or "not_ok")
        accepted = summary.get("accepted", 0)
        rejected = summary.get("rejected", 0)
        response_len = summary.get("response_len")
        suffix = f" accepted={accepted} rejected={rejected}"
        if response_len not in (None, ""):
            suffix += f" response_len={response_len}"
        return f"{error}{suffix}"

    response_path = rec.get("response")
    if isinstance(response_path, Path) and response_path.exists():
        text = _read_text_prefix(response_path, max_chars=1000)
        return _response_failure_kind(text)

    log_path = rec.get("log")
    if isinstance(log_path, Path) and log_path.exists():
        text = _read_text_prefix(log_path, max_chars=3000)
        if "existing board-refill task is queued or active" in text:
            return "skip_duplicate_refill"
        if "no dispatch-ready BEDC conversation tabs polling" in text:
            return "skip_no_dispatch_ready_tab"
        if "no compatible BEDC Project tabs polling" in text:
            return "skip_no_project_tab"
        if "zero-extraction hang" in text:
            return "waiting_zero_extraction_seen"
        if "submitted task=" in text:
            return "submitted_no_response_artifact_yet"
        if "server unreachable" in text:
            return "server_unreachable"
        if text.strip():
            return "log_only"

    if rec.get("prompt"):
        return "prompt_only"
    return "unknown"


def _format_refill_reject_suffix(summary: dict) -> str:
    reasons = summary.get("reject_reasons")
    examples = summary.get("reject_examples")
    if not isinstance(reasons, dict) or not reasons:
        return ""
    reason_items: list[tuple[str, int]] = []
    for key, value in reasons.items():
        try:
            count = int(value)
        except (TypeError, ValueError):
            continue
        reason_items.append((str(key), count))
    if not reason_items:
        return ""
    top_reason, top_count = sorted(reason_items, key=lambda kv: (-kv[1], kv[0]))[0]
    suffix = f" top_reject={top_reason}:{top_count}"
    if isinstance(examples, dict):
        example = str(examples.get(top_reason) or "").strip()
        if example:
            suffix += f" example={example[:60]}"
    return suffix


def _latest_local_gap_summary(rec: dict) -> dict | None:
    summary_path = rec.get("summary")
    if not isinstance(summary_path, Path) or not summary_path.exists():
        return None
    try:
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if summary.get("fallback") != "local_gap_scanner":
        return None
    return summary


def _refill_status_bucket(status: str) -> str:
    if status.startswith("local_gap_fallback_judge_unavailable"):
        if "claude_access_denied" in status:
            return "judge_unavailable:claude_access_denied"
        if "claude_not_logged_in" in status:
            return "judge_unavailable:claude_not_logged_in"
        return "judge_unavailable"
    if status.startswith("local_gap_fallback accepted="):
        return "local_gap_fallback_ok"
    if status.startswith("stopped_before_response"):
        return "oracle_transport_stopped"
    if status.startswith("timeout_waiting_for_response"):
        return "oracle_transport_timeout"
    if status.startswith("oracle_transport_"):
        return status.split()[0]
    if status.startswith("ok "):
        return "oracle_refill_ok"
    return status.split()[0] if status else "unknown"


def _coalesce_split_refill_records(records: dict[str, dict]) -> list[dict]:
    """Merge pre-run-id refill log/prompt artifacts that belong together.

    Older supervisor runs created the supervisor log timestamp before
    oracle_board_refill.py created the prompt timestamp, so one real refill can
    appear as two adjacent records. Keep this display-only and conservative:
    only merge a prompt-only record into a nearby submitted log-only record.
    """
    items = list(records.values())
    consumed: set[str] = set()
    log_records = [
        rec for rec in items
        if rec.get("log") and not rec.get("prompt") and not rec.get("response") and not rec.get("summary")
    ]
    artifact_records = [
        rec for rec in items
        if (rec.get("prompt") or rec.get("response") or rec.get("summary")) and not rec.get("log")
    ]
    for log_rec in log_records:
        if _infer_refill_status(log_rec) not in {
            "submitted_no_response_artifact_yet",
            "waiting_zero_extraction_seen",
        }:
            continue
        log_time = _refill_stem_time(log_rec.get("stem"))
        if log_time is None:
            continue
        nearest: dict | None = None
        nearest_delta = 999999.0
        for artifact_rec in artifact_records:
            stem = str(artifact_rec.get("stem") or "")
            if stem in consumed:
                continue
            artifact_time = _refill_stem_time(stem)
            if artifact_time is None:
                continue
            delta = abs((artifact_time - log_time).total_seconds())
            if delta <= 10.0 and delta < nearest_delta:
                nearest = artifact_rec
                nearest_delta = delta
        if nearest is None:
            continue
        for kind in ("prompt", "response", "summary"):
            if nearest.get(kind):
                log_rec[kind] = nearest.get(kind)
            if nearest.get(f"{kind}_mtime"):
                log_rec[f"{kind}_mtime"] = nearest.get(f"{kind}_mtime")
        log_rec["latest_mtime"] = max(
            float(log_rec.get("latest_mtime") or 0.0),
            float(nearest.get("latest_mtime") or 0.0),
        )
        merged = list(log_rec.get("merged_stems") or [])
        merged.append(str(nearest.get("stem") or ""))
        log_rec["merged_stems"] = merged
        consumed.add(str(nearest.get("stem") or ""))

    return [rec for rec in items if str(rec.get("stem") or "") not in consumed]


def render_board_refill() -> str:
    records: dict[str, dict] = {}
    patterns = [
        (BOARD_REFILL_LOG_DIR, "refill_*.prompt.txt", "prompt"),
        (BOARD_REFILL_LOG_DIR, "refill_*.response.md", "response"),
        (BOARD_REFILL_LOG_DIR, "refill_*.summary.json", "summary"),
        (SUPERVISOR_LOG_DIR, "refill_*.log", "log"),
    ]
    for directory, pattern, kind in patterns:
        if not directory.exists():
            continue
        for path in directory.glob(pattern):
            stem = _refill_stem(path)
            rec = records.setdefault(stem, {"stem": stem, "latest_mtime": 0.0})
            rec[kind] = path
            try:
                mtime = path.stat().st_mtime
                rec[f"{kind}_mtime"] = mtime
                rec["latest_mtime"] = max(float(rec["latest_mtime"]), mtime)
            except OSError:
                pass

    if not records:
        return "\n".join(["  (no board refill artifacts)", _next_refill_prompt_note()])

    ordered = sorted(
        _coalesce_split_refill_records(records),
        key=lambda item: float(item["latest_mtime"]),
        reverse=True,
    )
    now = datetime.now(timezone.utc)
    lines: list[str] = []
    for rec in ordered[:6]:
        mtime = float(rec.get("latest_mtime") or 0.0)
        age = "?"
        if mtime:
            age = _fmt_age((now - datetime.fromtimestamp(mtime, tz=timezone.utc)).total_seconds())
        artifacts = "+".join(
            name for name in ("prompt", "response", "summary", "log") if rec.get(name)
        )
        status = _infer_refill_status(rec)
        wait_seconds = _refill_wait_seconds(rec)
        prompt_note = _refill_prompt_note(rec)
        wait_note = f" wait={_fmt_age(wait_seconds)}" if wait_seconds is not None else ""
        merged = rec.get("merged_stems") or []
        merged_note = f" merged={','.join(merged)}" if merged else ""
        lines.append(
            f"  {rec.get('stem', '?')}: {age} ago   {artifacts or 'no_artifacts'}   "
            f"{status}{prompt_note}{wait_note}{merged_note}"
        )

    buckets: dict[str, int] = {}
    for rec in ordered[:12]:
        bucket = _refill_status_bucket(_infer_refill_status(rec))
        buckets[bucket] = buckets.get(bucket, 0) + 1
    if buckets:
        bucket_text = ", ".join(
            f"{name}={count}"
            for name, count in sorted(buckets.items(), key=lambda item: (-item[1], item[0]))
        )
        lines.append(f"  recent refill status buckets: {bucket_text}")
        if any(name.startswith("judge_unavailable") for name in buckets):
            lines.append(
                "  note: recent refill judge outages are Claude/Codex CLI-side; "
                "they are not BEDC oracle tab-refresh signals."
            )

    lines.append(_next_refill_prompt_note())

    latest = ordered[0]
    if latest.get("prompt") and not latest.get("response") and not latest.get("summary"):
        status = _infer_refill_status(latest)
        wait_seconds = _refill_wait_seconds(latest)
        if (
            status == "submitted_no_response_artifact_yet"
            and wait_seconds is not None
            and wait_seconds >= 900
        ):
            lines.append(
                "  alert: latest refill has waited >=15m with no response/summary; "
                "confirm oracle status before deciding whether to refresh a tab."
            )
        if status == "waiting_zero_extraction_seen":
            lines.append(
                "  alert: latest refill log has seen a zero-extraction hang; "
                "use oracle_client.py --status for the affected tab before any further action."
            )
        if status in {"prompt_only", "skip_duplicate_refill", "submitted_no_response_artifact_yet"}:
            lines.append(
                "  note: latest refill has no response/summary yet; use this to distinguish "
                "transport stalls from logic-gate rejection."
            )
    latest_status = _infer_refill_status(latest)
    latest_local_gap = _latest_local_gap_summary(latest)
    if (
        latest_local_gap is not None
        and _board_active_count() == 0
        and int(latest_local_gap.get("candidates_proposed") or 0) == 0
        and int(latest_local_gap.get("accepted") or 0) == 0
    ):
        lines.append(
            "  note: BOARD is dry and deterministic local gap fallback found 0 candidates; "
            "treat this as supply exhaustion, not a logic-gate or tab-refresh failure."
        )
        scanner_stats = latest_local_gap.get("scanner_stats") or {}
        if isinstance(scanner_stats, dict) and scanner_stats:
            lines.append(
                "  scanner: "
                f"gap_hits={scanner_stats.get('gap_hits', 0)} "
                f"namecert_raw={scanner_stats.get('raw_namecert_candidates', 0)} "
                f"prelimit={scanner_stats.get('prelimit_candidates', 0)} "
                f"emitted={scanner_stats.get('emitted_candidates', 0)}/"
                f"{scanner_stats.get('limit', 0)} "
                f"paper_covered_skips={scanner_stats.get('skip_known_paper_covered_title', 0)} "
                f"board/archive_skips={scanner_stats.get('skip_existing_board_or_archive_title', 0)} "
                f"nonsubstantive_skips={scanner_stats.get('skip_nonsubstantive_gap', 0)} "
                f"threshold_skips={scanner_stats.get('skip_below_threshold', 0)} "
                f"batch_dupes={scanner_stats.get('skip_duplicate_title_in_batch', 0)}"
            )
            by_kind = scanner_stats.get("gap_hits_by_kind") or {}
            if isinstance(by_kind, dict) and by_kind:
                kind_text = ", ".join(
                    f"{key}={value}"
                    for key, value in sorted(by_kind.items(), key=lambda item: str(item[0]))
                )
                lines.append(f"  scanner gap kinds: {kind_text}")
    if latest_status.startswith("local_gap_fallback_judge_unavailable"):
        lines.append(
            "  alert: local gap fallback found pre-gate candidates, but BOARD judge is unavailable; "
            "do not bypass the final maker/checker gate."
        )
        if "claude_not_logged_in" in latest_status:
            lines.append(
                "  action: restore Claude CLI auth for the BOARD judge; "
                "refreshing BEDC oracle tabs will not fix this outage."
            )
        if "claude_access_denied" in latest_status:
            lines.append(
                "  action: restore Claude CLI organization access for the BOARD judge; "
                "refreshing BEDC oracle tabs will not fix this outage."
            )
        if "codex_sandbox_init_failed" in latest_status:
            lines.append(
                "  note: Codex fallback also failed during sandbox app-server initialization."
            )
    return "\n".join(lines)


def render_board_spawn() -> str:
    if not BOARD_SPAWN_LATEST.exists():
        return "  (no shared board_spawn status recorded)"
    try:
        data = json.loads(BOARD_SPAWN_LATEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "  (unreadable shared board_spawn status)"
    ts = _parse_iso(data.get("ts"))
    age = _fmt_age((datetime.now(timezone.utc) - ts).total_seconds()) if ts else "?"
    appended = data.get("appended_ids") if isinstance(data.get("appended_ids"), list) else []
    lines = [
        (
            f"  latest: {age} ago ok={data.get('ok')} "
            f"input=codex:{data.get('codex_input')} oracle:{data.get('oracle_input')} "
            f"alive=codex:{data.get('codex_alive')} oracle:{data.get('oracle_alive')}"
        ),
        (
            f"  outcome: accepted={data.get('accepted_count')} "
            f"held={data.get('held_count', 0)} "
            f"rejected={data.get('rejected_count')} cheap_drops={data.get('cheap_drop_count')} "
            f"appended={len(appended)}"
        ),
    ]
    error_kind = str(data.get("error_kind") or "")
    if error_kind:
        lines.append(f"  error_kind: {error_kind}")
    lines.extend(_board_judge_action_lines(error_kind))
    return "\n".join(lines)


def render_loning_assimilation() -> str:
    if not LONING_ASSIMILATION_JOURNAL.exists():
        return "  (no loning assimilation state)"
    try:
        lines = LONING_ASSIMILATION_JOURNAL.read_text(
            encoding="utf-8", errors="replace"
        ).splitlines()
    except OSError as exc:
        return f"  unavailable: {exc}"
    for line in reversed(lines):
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(rec, dict):
            continue
        checked_at = _parse_iso(rec.get("checked_at"))
        age = _fmt_age((datetime.now(timezone.utc) - checked_at).total_seconds()) if checked_at else "?"
        counts = rec.get("signal_counts") or {}
        count_text = ", ".join(
            f"{k}={v}" for k, v in sorted(counts.items(), key=lambda kv: str(kv[0]))
        )
        out = [
            (
                f"  checked: {age} ago   relevant_commits={rec.get('relevant_commits', '?')} "
                f"watch_entries={rec.get('watch_entries', '?')}"
            )
        ]
        watch_ts = _latest_jsonl_ts(LONING_WATCH_JOURNAL)
        if checked_at and watch_ts and watch_ts > checked_at:
            lag = _fmt_age((watch_ts - checked_at).total_seconds())
            out.append(
                "  lag: loning_watch is "
                f"{lag} newer than assimilation "
                f"(watch={watch_ts.isoformat()} assimilation={checked_at.isoformat()})"
            )
        if count_text:
            out.append(f"  signals: {count_text}")
        if rec.get("advice") or rec.get("prompt_block"):
            out.append("  note: legacy advice fields ignored; only signal_counts are used")
        return "\n".join(out)
    return "  (no parseable loning assimilation records)"


def _discovery_status(data: dict) -> str:
    mode = str(data.get("_mode") or "?")
    if data.get("ok") is False:
        stage = str(data.get("stage") or "?")
        error = str(data.get("error") or "").replace("\n", " ")
        if "not logged in" in error.lower() and "operation not permitted" in error.lower():
            return (
                f"{mode} failed stage={stage} "
                "discovery_judge_unavailable:claude_auth+codex_sandbox"
            )
        if "not logged in" in error.lower() or "does not have access to claude" in error.lower():
            return f"{mode} failed stage={stage} discovery_judge_unavailable:claude_auth"
        if "operation not permitted" in error.lower():
            return f"{mode} failed stage={stage} discovery_judge_unavailable:codex_sandbox"
        return f"{mode} failed stage={stage} error={error[:90]}"
    kept = data.get("kept") if isinstance(data.get("kept"), list) else []
    appended = data.get("appended_ids") if isinstance(data.get("appended_ids"), list) else []
    board_spawn = data.get("board_spawn") if isinstance(data.get("board_spawn"), dict) else {}
    rejected = board_spawn.get("rejected") if isinstance(board_spawn.get("rejected"), list) else []
    suffix = f"{mode} ok kept={len(kept)} appended={len(appended)}"
    if rejected:
        reasons: dict[str, int] = {}
        for item in rejected:
            if not isinstance(item, dict):
                continue
            reason = str(item.get("reason") or "unspecified")
            reasons[reason] = reasons.get(reason, 0) + 1
        if reasons:
            reason, count = sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0]))[0]
            suffix += f" top_reject={reason}:{count}"
    return suffix


def _latest_supervisor_discovery_run() -> tuple[float, Path, str] | None:
    if not SUPERVISOR_LOG_DIR.exists():
        return None
    paths: list[Path] = []
    for pattern in ("probe_*.log", "curriculum_*.log", "paper_review_*.log", "curator_*.log"):
        paths.extend(SUPERVISOR_LOG_DIR.glob(pattern))
    latest: tuple[float, Path, str] | None = None
    for path in paths:
        try:
            mtime = path.stat().st_mtime
            lines = [
                line.strip()
                for line in path.read_text(encoding="utf-8", errors="replace").splitlines()
                if line.strip()
            ]
        except OSError:
            continue
        detail = lines[-1] if lines else "(no log output yet)"
        item = (mtime, path, detail)
        if latest is None or item[0] > latest[0]:
            latest = item
    return latest


def _discovery_run_timeout_seconds(path: Path) -> int:
    if path.name.startswith("curator_"):
        return 2400
    return 1800


def _completed_discovery_artifact(detail: str) -> Path | None:
    match = re.search(r"\bfull record:\s+(.+?\.json)\s*$", detail)
    if not match:
        return None
    path = Path(match.group(1))
    if not path.is_absolute():
        path = REPO_ROOT / path
    if path.exists():
        return path
    return None


def _format_pending_discovery_run(mtime: float, path: Path, detail: str) -> str:
    now = datetime.now(timezone.utc)
    age_seconds = (now - datetime.fromtimestamp(mtime, tz=timezone.utc)).total_seconds()
    age = _fmt_age(age_seconds)
    timeout = _discovery_run_timeout_seconds(path)
    label = "pending/in-flight" if age_seconds <= timeout else "pending/overdue"
    return (
        f"  {label}: supervisor {path.stem} log updated {age} ago; "
        f"timeout={_fmt_age(timeout)}; last line: {detail[:120]}"
    )


def render_discovery_lane() -> str:
    supervisor_run = _latest_supervisor_discovery_run()
    if not DISCOVERY_LOG_DIR.exists():
        if supervisor_run:
            mtime, path, detail = supervisor_run
            return (
                "  (no discovery artifacts)\n"
                + _format_pending_discovery_run(mtime, path, detail)
            )
        return "  (no discovery artifacts)"
    records: list[tuple[float, Path, dict]] = []
    for path in DISCOVERY_LOG_DIR.glob("*.json"):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            mtime = path.stat().st_mtime
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(data, dict):
            continue
        data["_mode"] = path.name.split("_", 1)[0]
        records.append((mtime, path, data))
    if not records:
        if supervisor_run:
            mtime, path, detail = supervisor_run
            return (
                "  (no parseable discovery artifacts)\n"
                + _format_pending_discovery_run(mtime, path, detail)
            )
        return "  (no parseable discovery artifacts)"
    records.sort(key=lambda item: item[0], reverse=True)
    now = datetime.now(timezone.utc)
    lines: list[str] = []
    recent_judge_outage = False
    for mtime, path, data in records[:6]:
        age = _fmt_age((now - datetime.fromtimestamp(mtime, tz=timezone.utc)).total_seconds())
        status = _discovery_status(data)
        lines.append(f"  {path.stem}: {age} ago   {status}")
        if "discovery_judge_unavailable" in status:
            recent_judge_outage = True
    latest = records[0][2]
    latest_status = _discovery_status(latest)
    if "discovery_judge_unavailable" in latest_status:
        lines.append(
            "  alert: discovery lane cannot currently run its maker/checker path; "
            "refreshing BEDC oracle tabs will not fix Claude/Codex CLI auth or sandbox failures."
        )
    elif recent_judge_outage:
        lines.append(
            "  note: a recent discovery maker/checker outage was Claude/Codex CLI-side; "
            "it is not a BEDC oracle tab-refresh signal."
        )
    if supervisor_run:
        run_mtime, run_path, detail = supervisor_run
        latest_artifact_mtime = records[0][0]
        if run_mtime > latest_artifact_mtime and not _completed_discovery_artifact(detail):
            lines.append(_format_pending_discovery_run(run_mtime, run_path, detail))
    return "\n".join(lines)


def _read_research_latest_counts() -> dict[str, int]:
    counts = {"packets": 0, "ready": 0, "blocked": 0, "oracle_after_codex": 0}
    if not RESEARCH_CANDIDATES_LATEST.exists():
        return counts
    try:
        lines = RESEARCH_CANDIDATES_LATEST.read_text(
            encoding="utf-8",
            errors="replace",
        ).splitlines()
    except OSError:
        return counts
    for line in lines:
        match = re.match(r"-\s+([a-z_]+):\s+(\d+)\s*$", line.strip())
        if not match:
            continue
        key, value = match.groups()
        if key == "oracle_recommended":
            key = "oracle_after_codex"
        elif key == "oracle_recommended_after_codex":
            key = "oracle_after_codex"
        if key in counts:
            counts[key] = int(value)
    return counts


def _read_research_latest_profiles() -> dict[str, str]:
    profiles: dict[str, str] = {}
    if not RESEARCH_CANDIDATES_LATEST.exists():
        return profiles
    try:
        lines = RESEARCH_CANDIDATES_LATEST.read_text(
            encoding="utf-8",
            errors="replace",
        ).splitlines()
    except OSError:
        return profiles
    for line in lines:
        match = re.match(r"-\s+(ready_(?:budget|difficulty|oracle_mode)):\s+(.+?)\s*$", line.strip())
        if match:
            profiles[match.group(1)] = match.group(2)
    return profiles


def _read_research_ready_titles(limit: int = 5) -> list[str]:
    if not RESEARCH_CANDIDATES_LATEST.exists():
        return []
    try:
        lines = RESEARCH_CANDIDATES_LATEST.read_text(
            encoding="utf-8",
            errors="replace",
        ).splitlines()
    except OSError:
        return []
    titles: list[str] = []
    in_ready = False
    for line in lines:
        stripped = line.strip()
        if stripped == "## Ready":
            in_ready = True
            continue
        if in_ready and stripped.startswith("## "):
            break
        if not in_ready or not stripped.startswith("- "):
            continue
        title = stripped[2:].strip()
        if " [" in title:
            title = title.rsplit(" [", 1)[0].strip()
        if title:
            titles.append(title)
        if len(titles) >= limit:
            break
    return titles


def render_research_candidate_lane() -> str:
    counts = _read_research_latest_counts()
    profiles = _read_research_latest_profiles()
    lines = [
        (
            f"  latest packets={counts['packets']} ready={counts['ready']} "
            f"blocked={counts['blocked']} oracle_after_codex={counts['oracle_after_codex']}"
        )
    ]
    if counts["ready"] and profiles:
        if profiles.get("ready_budget"):
            lines.append(f"  ready budget: {profiles['ready_budget']}")
        if profiles.get("ready_difficulty"):
            lines.append(f"  ready difficulty: {profiles['ready_difficulty']}")
        if profiles.get("ready_oracle_mode"):
            lines.append(f"  ready oracle modes: {profiles['ready_oracle_mode']}")
    if not RESEARCH_BOARD_SPAWN_LATEST.exists():
        lines.append("  append status: no research board_spawn attempt recorded")
        return "\n".join(lines)
    try:
        data = json.loads(RESEARCH_BOARD_SPAWN_LATEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        lines.append("  append status: unreadable research board_spawn status")
        return "\n".join(lines)
    ts = _parse_iso(data.get("ts"))
    age = _fmt_age((datetime.now(timezone.utc) - ts).total_seconds()) if ts else "?"
    appended = data.get("appended_ids") if isinstance(data.get("appended_ids"), list) else []
    lines.append(
        (
            f"  last append: {age} ago ok={data.get('ok')} ready={data.get('ready_count')} "
            f"accepted={data.get('accepted')} held={data.get('held', 0)} "
            f"rejected={data.get('rejected')} "
            f"appended={len(appended)}"
        )
    )
    error_kind = str(data.get("error_kind") or "")
    if error_kind:
        lines.append(f"  last append error_kind: {error_kind}")
    lines.extend(_board_judge_action_lines(error_kind))
    if counts["ready"] and "board_judge_unavailable" in error_kind:
        titles = _read_research_ready_titles(limit=5)
        if titles:
            lines.append("  held ready behind shared judge outage:")
            for title in titles:
                lines.append(f"    - {title}")
    return "\n".join(lines)


def _latest_jsonl_record(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None
    for line in reversed(lines):
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(rec, dict):
            if path == PI_RECENT_CYCLES and rec.get("review_source") == "test":
                continue
            return rec
    return None


def _parse_pi_ts(value: object) -> datetime | None:
    """PI cycle records historically used local naive timestamps."""
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip()
    if text.endswith("Z") or re.search(r"[+-]\d\d:\d\d$", text):
        return _parse_iso(text)
    try:
        ts = datetime.fromisoformat(text)
    except ValueError:
        return None
    local_tz = datetime.now().astimezone().tzinfo
    return ts.replace(tzinfo=local_tz).astimezone(timezone.utc)


def render_pi_agent() -> str:
    rec = _latest_jsonl_record(PI_RECENT_CYCLES)
    if not rec:
        return "  (no PI agent cycles recorded)"
    ts = _parse_pi_ts(rec.get("ts"))
    age = _fmt_age((datetime.now(timezone.utc) - ts).total_seconds()) if ts else "?"
    summary = rec.get("snapshot_summary") if isinstance(rec.get("snapshot_summary"), dict) else {}
    rates = summary.get("completion_rates") if isinstance(summary.get("completion_rates"), dict) else {}
    track = summary.get("codex_track_summary") if isinstance(summary.get("codex_track_summary"), dict) else {}
    lines = [
        (
            f"  latest: {age} ago ok={rec.get('ok')} health={rec.get('plan_health')} "
            f"source={rec.get('review_source')}"
        ),
        (
            f"  actions: planned={rec.get('plan_action_count')} applied={rec.get('applied_count')} "
            f"inbox={rec.get('inbox_count')} deepen_emitted={rec.get('deepen_emitted')}"
        ),
    ]
    if not rec.get("ok"):
        error_kind = str(rec.get("error_kind") or "").strip()
        if error_kind:
            lines.append(f"  error_kind: {error_kind}")
            lines.extend(_planner_action_lines(error_kind))
        else:
            lines.append("  error_kind: planner_failed_without_classified_reason")
    if rates:
        rate_text = ", ".join(f"{k}={v}" for k, v in rates.items())
        lines.append(f"  completion rates: {rate_text}")
    if track:
        parts = []
        for key in ("v2_total", "codex_close", "oracle_path", "codex_close_rate"):
            if key in track:
                parts.append(f"{key}={track.get(key)}")
        if parts:
            lines.append("  codex track: " + ", ".join(parts))
    concerns = [str(c) for c in (rec.get("escalated_concerns") or []) if str(c).strip()]
    if concerns:
        lines.append("  escalated concerns: " + " | ".join(c[:90] for c in concerns[:3]))
    gauntlet = rec.get("gauntlet_results") if isinstance(rec.get("gauntlet_results"), list) else []
    failed = [g for g in gauntlet if isinstance(g, dict) and not g.get("pass_all")]
    if failed:
        for item in failed[:3]:
            action = item.get("action") if isinstance(item.get("action"), dict) else {}
            name = str(action.get("action") or "?")
            summary_text = str(item.get("summary") or "").replace("\n", " ")
            lines.append(f"  blocked: {name} — {summary_text[:140]}")
    if rec.get("deepen_emitted"):
        suppress_ts = _git_commit_ts(PI_DRY_BOARD_SUPPRESSION_COMMIT)
        if ts and suppress_ts and ts < suppress_ts:
            lines.append(
                "  note: latest deepen emission predates dry-board suppression "
                f"({PI_DRY_BOARD_SUPPRESSION_COMMIT}); watch the next PI cycle."
            )
    return "\n".join(lines)


def _latest_jsonl_ts(path: Path) -> datetime | None:
    if not path.exists():
        return None
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None
    for line in reversed(lines):
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(rec, dict):
            ts = _parse_iso(rec.get("checked_at") or rec.get("ts") or rec.get("updated_at"))
            if ts:
                return ts
    return None


def render_target_table(limit: int = 80) -> str:
    from lifecycle import derive_failure_kind, decide_next_action
    items: list[dict] = []
    if not STATE_DIR.exists():
        return "  (no state files)"
    for f in sorted(STATE_DIR.glob("*.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(d, dict):
            continue
        if not d.get("target_id") and not (d.get("stage1_verdict") or d.get("stage2")):
            continue
        kind = derive_failure_kind(d)
        action = decide_next_action({**d, "failure_kind": kind})
        attempts = d.get("attempts", 1)
        items.append({
            "target_id": d.get("target_id") or f.stem,
            "kind": kind,
            "attempts": attempts,
            "action": action,
            "title": (d.get("title") or "")[:40],
        })

    def priority(item: dict) -> tuple[int, str]:
        action = str(item.get("action") or "")
        kind = str(item.get("kind") or "")
        if action not in {"skip", ""}:
            return (0, str(item.get("target_id") or ""))
        if kind not in {"none", "pre_flight_duplicate", "stage2_duplicate_content"}:
            return (1, str(item.get("target_id") or ""))
        return (2, str(item.get("target_id") or ""))

    ordered = sorted(items, key=priority)
    shown = ordered if limit <= 0 else ordered[:limit]
    summary: dict[tuple[str, str], list[str]] = {}
    for item in items:
        key = (str(item.get("action") or "?"), str(item.get("kind") or "?"))
        summary.setdefault(key, []).append(str(item.get("target_id") or "?"))
    rows: list[str] = []
    for (action, kind), targets in sorted(
        summary.items(),
        key=lambda kv: (kv[0][0] != "alert_user", kv[0][0], -len(kv[1]), kv[0][1]),
    )[:8]:
        rows.append(
            f"  summary {action:<14} {kind:<28} {len(targets):>3} "
            f"examples={', '.join(targets[:4])}"
        )
    rows.append(f"  {'TARGET':<8} {'KIND':<28} {'ATTEMPTS':<10} {'NEXT':<14} TITLE")
    for item in shown:
        rows.append(
            f"  {item.get('target_id','?'):<8} {item.get('kind','?'):<28} "
            f"{str(item.get('attempts', 1)):<10} {item.get('action','?'):<14} "
            f"{item.get('title','')}"
        )
    if limit > 0 and len(ordered) > len(shown):
        rows.append(f"  ... {len(ordered) - len(shown)} lower-priority rows omitted; use --target-limit 0 for full table")
    return "\n".join(rows)


def render_histogram() -> str:
    from lifecycle import histogram, FAILURE_KINDS
    hist = histogram()
    if not hist:
        return "  (no completed targets)"
    width = max(len(k) for k in hist) if hist else 30
    out: list[str] = []
    total = sum(hist.values())
    for kind, n in sorted(hist.items(), key=lambda kv: -kv[1]):
        bar = "█" * min(40, n * 2)
        out.append(f"  {kind:<{width}}  {n:>3}  {bar}")
    success = hist.get("none", 0)
    skipped = hist.get("pre_flight_duplicate", 0) + hist.get("stage2_duplicate_content", 0)
    attempted = total - skipped
    out.append("")
    if attempted > 0:
        out.append(f"  success rate (excl. paper duplicates): {success}/{attempted}  ({100.0 * success / attempted:.0f}%)")
    else:
        out.append(f"  no genuine attempts yet (all {total} targets matched existing paper content)")
    return "\n".join(out)


def render_reject_clusters() -> str:
    if not TARGETS_DIR.exists():
        return "  (no targets dir)"
    counts: dict[str, int] = {}
    examples: dict[str, str] = {}
    for f in TARGETS_DIR.glob("*/stage2_result.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if d.get("verdict") not in ("reject", "compile_failed"):
            continue
        rejection_codes = list(d.get("rejection_codes") or [])
        for code in rejection_codes:
            cat = _stage2_reject_category(str(code or ""))
            counts[cat] = counts.get(cat, 0) + 1
            examples.setdefault(cat, f.parent.name)
        reasons = [] if rejection_codes else list(d.get("rejection_reasons") or [])
        reasons.extend(d.get("compile_errors") or [])
        for r in reasons:
            cat = _stage2_reject_category(str(r or ""))
            counts[cat] = counts.get(cat, 0) + 1
            examples.setdefault(cat, f.parent.name)
    if not counts:
        return "  (no Stage 2 rejects yet)"
    return "\n".join(
        f"  {k:<38}  {v:>3}  {'█' * min(40, v * 2)}  example={examples.get(k, '-')}"
        for k, v in sorted(counts.items(), key=lambda kv: -kv[1])
    )


def _stage2_reject_category(reason: str) -> str:
    """Normalize Stage 2 checklist prose into audit-ready buckets."""
    r_low = reason.lower()
    if "duplicate \\leanchecked" in r_low or "duplicate \\leantarget" in r_low:
        return "duplicate_lean_marker"
    if r_low in {
        "bad_target_file",
        "line_cap",
        "empty_content",
        "compile_failed",
        "external_provenance_leak",
        "killo_review_reject",
    }:
        return r_low
    if "build invariant" in r_low:
        return "build_invariant"
    if "undefined control sequence" in r_low or "undefined macro" in r_low:
        return "undefined_macro"
    if "content duplication" in r_low:
        return "content_duplication"
    if "non-latex" in r_low or "trailing" in r_low:
        return "non_latex_trailing"
    if (
        "800-line" in r_low
        or "line cap" in r_low
        or "far past the 800" in r_low
        or "exceed 800 lines" in r_low
    ):
        return "line_cap"
    if (
        ("target" in r_low and "does not exist" in r_low)
        or "not a concrete body file" in r_low
    ):
        return "bad_target_file"
    if (
        "transport-style" in r_low
        or "without a transport-citation" in r_low
        or "without a transport citation" in r_low
        or "implicit transport step" in r_low
    ):
        return "implicit_transport_without_citation"
    if "implicit inversion" in r_low or "no labeled theorem/lemma" in r_low:
        return "missing_inversion_or_projection_lemma"
    if "display math" in r_low or "undefined control sequence" in r_low:
        return "latex_layout"
    if "operatorname" in r_low or "macro convention" in r_low:
        return "macro_convention"
    if "no theorem" in r_low or "no \\begin{theorem}" in r_low or "contains json" in r_low:
        return "missing_appendable_latex_environment"
    m = re.search(r"item\s*(\d+)", r_low)
    if m:
        return f"checklist_item_{m.group(1)}"
    return "other"


def render_logic_audit_warnings() -> str:
    if not TARGETS_DIR.exists():
        return "  (no targets dir)"
    counts: dict[str, int] = {}
    examples: dict[str, str] = {}
    failed_counts: dict[str, int] = {}
    failed_examples: dict[str, str] = {}
    audited = 0
    warned = 0
    stale_warning_artifacts = 0
    failed_stale_warning_artifacts = 0
    failed_audited = 0
    failed_warned = 0
    for f in TARGETS_DIR.glob("*/stage2_result.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        audit = d.get("logic_audit") or {}
        if not audit:
            continue
        landed = (
            d.get("verdict") == "accept"
            and d.get("appended") is True
            and d.get("compile_ok") is True
        )
        warnings = audit.get("warnings") or []
        target = f.parent.name
        if landed:
            current_warnings = _current_logic_audit_warnings(target)
            if current_warnings is not None:
                if warnings and current_warnings != warnings:
                    stale_warning_artifacts += 1
                warnings = current_warnings
            audited += 1
            if warnings:
                warned += 1
        else:
            current_warnings = _current_logic_audit_warnings(target)
            if current_warnings is not None:
                if warnings and current_warnings != warnings:
                    failed_stale_warning_artifacts += 1
                warnings = current_warnings
            failed_audited += 1
            if warnings:
                failed_warned += 1
        for warning in warnings:
            if not isinstance(warning, dict):
                continue
            code = str(warning.get("code") or "unknown")
            if landed:
                counts[code] = counts.get(code, 0) + 1
                examples.setdefault(code, target)
            else:
                failed_counts[code] = failed_counts.get(code, 0) + 1
                failed_examples.setdefault(code, target)
    lines = [f"  accepted audited={audited} warned={warned}"]
    if not counts:
        lines.append("  accepted warnings: none")
    if stale_warning_artifacts:
        lines.append(f"  accepted stale warning artifacts ignored={stale_warning_artifacts}")
    for code, n in sorted(counts.items(), key=lambda kv: -kv[1])[:8]:
        lines.append(f"  {code:<48} {n:>3}  example={examples.get(code, '?')}")
    if failed_audited:
        lines.append(
            f"  failed/blocked audited={failed_audited} warned={failed_warned} "
            "(not paper body)"
        )
    if failed_stale_warning_artifacts:
        lines.append(
            "  failed/blocked stale warning artifacts ignored="
            f"{failed_stale_warning_artifacts}"
        )
    for code, n in sorted(failed_counts.items(), key=lambda kv: -kv[1])[:5]:
        lines.append(
            f"  failed/blocked {code:<33} {n:>3}  "
            f"example={failed_examples.get(code, '?')}"
        )
    return "\n".join(lines)


def _current_logic_audit_warnings(target_slug: str) -> list[dict[str, str]] | None:
    raw_path = TARGETS_DIR / target_slug / "raw_oracle_latex.md"
    if not raw_path.exists():
        return None
    try:
        import killo_golden_writeback
        raw_text = raw_path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return None
    fenced = re.search(r"```(?:latex)?\s*(.*?)```", raw_text, re.DOTALL)
    if fenced:
        content = fenced.group(1)
    else:
        first = re.search(r"\\begin\{(?:theorem|lemma|proposition|corollary|definition)\}", raw_text)
        content = raw_text[first.start():] if first else raw_text
    audit = killo_golden_writeback._logic_surface_audit(content)
    warnings = audit.get("warnings") or []
    return [warning for warning in warnings if isinstance(warning, dict)]


def render_recent_commits(n: int = 5) -> str:
    out = _git(["log", "--oneline", f"-{n}"])
    return "\n".join(f"  {ln}" for ln in out.splitlines())


def render_supervisor_tail(n: int = 8) -> str:
    if not SUPERVISOR_LOG.exists():
        return "  (no supervisor log)"
    try:
        lines = SUPERVISOR_LOG.read_text(encoding="utf-8").splitlines()[-n:]
    except OSError:
        return "  (could not read supervisor log)"
    return "\n".join(f"  {ln}" for ln in lines) if lines else "  (empty)"


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC bedc-deep dashboard")
    parser.add_argument("--no-clear", action="store_true", help="Skip clearing the screen")
    parser.add_argument("--target-limit", type=int, default=80, help="Max target lifecycle rows; 0 shows all")
    args = parser.parse_args()

    if not args.no_clear and sys.stdout.isatty():
        sys.stdout.write("\x1b[2J\x1b[H")

    print(f"BEDC bedc-deep dashboard  •  {_now_iso()}")
    print(_section("Server (:8767)"))
    print(render_server(_safe_get_server()))
    print(_section("BOARD"))
    print(render_board())
    print(_section("Active BOARD Targets"))
    print(render_active_board_targets())
    print(_section("Candidate Inbox"))
    print(render_candidate_inbox())
    print(_section("Board Refill"))
    print(render_board_refill())
    print(_section("Board Spawn"))
    print(render_board_spawn())
    print(_section("Discovery Lane"))
    print(render_discovery_lane())
    print(_section("Research Candidate Lane"))
    print(render_research_candidate_lane())
    print(_section("PI Agent"))
    print(render_pi_agent())
    print(_section("Loning Assimilation"))
    print(render_loning_assimilation())
    print(_section("Target lifecycle"))
    print(render_target_table(limit=args.target_limit))
    print(_section("failure_kind histogram"))
    print(render_histogram())
    print(_section("Stage 2 reject clusters"))
    print(render_reject_clusters())
    print(_section("Stage 2 logic audit"))
    print(render_logic_audit_warnings())
    print(_section("Recent commits"))
    print(render_recent_commits())
    print(_section("Supervisor tail"))
    print(render_supervisor_tail())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

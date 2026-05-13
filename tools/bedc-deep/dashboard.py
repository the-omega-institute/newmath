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
LONING_ASSIMILATION_JOURNAL = STATE_DIR / "loning_assimilation.jsonl"
LONING_WATCH_JOURNAL = STATE_DIR / "loning_watch.jsonl"
ORACLE_SERVER_URL = "http://localhost:8767"

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
    out = [
        f"  diagnosis: {diag}",
        f"  agents:    {busy}/{cap} busy   queue={queue}   completed={completed}",
        f"  recent agents (last 120s): {active_recent}",
    ]
    for k, v in (s.get("agents") or {}).items():
        out.append(f"    busy {k}: task={v.get('task_id','?')} elapsed={v.get('elapsed','?')}s")
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


def _infer_refill_status(rec: dict) -> str:
    summary_path = rec.get("summary")
    if isinstance(summary_path, Path) and summary_path.exists():
        try:
            summary = json.loads(summary_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return "summary_unreadable"
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
    prompt_records = [
        rec for rec in items
        if rec.get("prompt") and not rec.get("log") and not rec.get("response") and not rec.get("summary")
    ]
    for log_rec in log_records:
        if _infer_refill_status(log_rec) != "submitted_no_response_artifact_yet":
            continue
        log_time = _refill_stem_time(log_rec.get("stem"))
        if log_time is None:
            continue
        nearest: dict | None = None
        nearest_delta = 999999.0
        for prompt_rec in prompt_records:
            stem = str(prompt_rec.get("stem") or "")
            if stem in consumed:
                continue
            prompt_time = _refill_stem_time(stem)
            if prompt_time is None:
                continue
            delta = abs((prompt_time - log_time).total_seconds())
            if delta <= 10.0 and delta < nearest_delta:
                nearest = prompt_rec
                nearest_delta = delta
        if nearest is None:
            continue
        log_rec["prompt"] = nearest.get("prompt")
        log_rec["prompt_mtime"] = nearest.get("prompt_mtime")
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
        return "  (no board refill artifacts)"

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
        merged = rec.get("merged_stems") or []
        merged_note = f" merged={','.join(merged)}" if merged else ""
        lines.append(
            f"  {rec.get('stem', '?')}: {age} ago   {artifacts or 'no_artifacts'}   {status}{merged_note}"
        )

    latest = ordered[0]
    if latest.get("prompt") and not latest.get("response") and not latest.get("summary"):
        status = _infer_refill_status(latest)
        if status in {"prompt_only", "skip_duplicate_refill", "submitted_no_response_artifact_yet"}:
            lines.append(
                "  note: latest refill has no response/summary yet; use this to distinguish "
                "transport stalls from logic-gate rejection."
            )
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
        advice = [str(item) for item in (rec.get("advice") or []) if str(item).strip()]
        for item in advice[:3]:
            out.append(f"  advice: {item}")
        if len(advice) > 3:
            out.append(f"  advice: ... {len(advice) - 3} more")
        return "\n".join(out)
    return "  (no parseable loning assimilation records)"


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
    for f in TARGETS_DIR.glob("*/stage2_result.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if d.get("verdict") not in ("reject", "compile_failed"):
            continue
        for r in d.get("rejection_reasons") or []:
            r_low = (r or "").lower()
            cat = "other"
            m = re.search(r"item\s*(\d+)", r_low)
            if m:
                cat = f"item_{m.group(1)}"
            elif "build invariant" in r_low:
                cat = "build_invariant"
            elif "content duplication" in r_low:
                cat = "content_duplication"
            elif "non-latex" in r_low or "trailing" in r_low:
                cat = "non_latex_trailing"
            counts[cat] = counts.get(cat, 0) + 1
    if not counts:
        return "  (no Stage 2 rejects yet)"
    return "\n".join(
        f"  {k:<24}  {v:>3}  {'█' * min(40, v * 2)}"
        for k, v in sorted(counts.items(), key=lambda kv: -kv[1])
    )


def render_logic_audit_warnings() -> str:
    if not TARGETS_DIR.exists():
        return "  (no targets dir)"
    counts: dict[str, int] = {}
    examples: dict[str, str] = {}
    audited = 0
    warned = 0
    for f in TARGETS_DIR.glob("*/stage2_result.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        audit = d.get("logic_audit") or {}
        if not audit:
            continue
        audited += 1
        warnings = audit.get("warnings") or []
        if warnings:
            warned += 1
        target = f.parent.name
        for warning in warnings:
            if not isinstance(warning, dict):
                continue
            code = str(warning.get("code") or "unknown")
            counts[code] = counts.get(code, 0) + 1
            examples.setdefault(code, target)
    if not counts:
        return f"  audited={audited} warned={warned} (no post-write logic warnings)"
    lines = [f"  audited={audited} warned={warned}"]
    for code, n in sorted(counts.items(), key=lambda kv: -kv[1])[:8]:
        lines.append(f"  {code:<48} {n:>3}  example={examples.get(code, '?')}")
    return "\n".join(lines)


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
    print(_section("Candidate Inbox"))
    print(render_candidate_inbox())
    print(_section("Board Refill"))
    print(render_board_refill())
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

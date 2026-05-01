#!/usr/bin/env python3
"""BEDC PI agent — bounded operator action plan from a Claude consultation.

The supervisor calls this in place of its prior read-only claude review.
The PI agent receives a snapshot of the live pipeline (server, BOARD,
state files, supervisor tail, recent commits, reject clusters), asks
Claude for an action plan, and applies the autonomous subset directly.
Risky proposals land in .human_inbox.md for the operator to review.

Hard boundaries enforced by this module (defense in depth — the prompt
also forbids them):
- never edits files under lean4/ or papers/bedc/parts/
- never cancels oracle tasks mid-flight (cancel_target only goes to inbox)
- never changes --parallel mid-flight (adjust_parallel only goes to inbox)
- never edits prompts/* files (prompt_repair only goes to inbox)

State written:
  state/pi_journal.jsonl       one line per PI cycle, full record
  state/concern_counts.json    persisted counter for repeated concerns
  .human_inbox.md              actionable suggestions for the operator
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "state"
PROMPT_PATH = SCRIPT_DIR / "prompts" / "pi_agent.txt"
SUPERVISOR_LOG = STATE_DIR / "supervisor_logs" / "supervisor.log"
PI_JOURNAL = STATE_DIR / "pi_journal.jsonl"
CONCERN_COUNTS_PATH = STATE_DIR / "concern_counts.json"
HUMAN_INBOX = SCRIPT_DIR / ".human_inbox.md"
ORACLE_SERVER_URL = "http://localhost:8767"

ESCALATE_AFTER_REPEATS = 2
PI_TIMEOUT_S = 1200

sys.path.insert(0, str(SCRIPT_DIR))


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _server_status() -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=3) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception as exc:
        return {"_error": str(exc)}


def _read_tail(path: Path, n: int = 30) -> str:
    if not path.exists():
        return "(file not present)"
    try:
        return "\n".join(path.read_text(encoding="utf-8").splitlines()[-n:])
    except OSError:
        return "(could not read)"


def _state_summary(limit: int = 60) -> dict:
    rows: list[dict] = []
    if not STATE_DIR.exists():
        return {"rows": rows, "histogram": {}}
    histogram: dict[str, int] = {}
    for f in sorted(STATE_DIR.glob("*.json"))[:limit]:
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        kind = d.get("failure_kind")
        if not kind:
            try:
                from lifecycle import derive_failure_kind
                kind = derive_failure_kind(d)
            except Exception:
                kind = "unknown"
        histogram[kind] = histogram.get(kind, 0) + 1
        rows.append({
            "target_id": d.get("target_id"),
            "title": (d.get("title") or "")[:60],
            "failure_kind": kind,
            "attempts": d.get("attempts", 1),
            "next_action": d.get("next_action", "skip"),
            "stage1_verdict": d.get("stage1_verdict"),
            "stage2_verdict": (d.get("stage2") or {}).get("verdict"),
        })
    return {"rows": rows, "histogram": histogram}


def _board_unfinished() -> int:
    try:
        from dispatch_bedc_target import parse_board
        targets = parse_board()
    except Exception:
        return 0
    n = 0
    for t in targets.values():
        if (STATE_DIR / f"{t.slug}.json").exists():
            continue
        if (STATE_DIR / t.slug / ".in_progress").exists():
            continue
        n += 1
    return n


def _stage2_reject_clusters() -> dict:
    targets_dir = SCRIPT_DIR / "targets"
    if not targets_dir.exists():
        return {}
    counts: dict[str, int] = {}
    for f in targets_dir.glob("*/stage2_result.json"):
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
    return counts


def _recent_commits(n: int = 5) -> list[str]:
    try:
        out = subprocess.run(
            ["git", "log", "--oneline", f"-{n}"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=5,
        ).stdout
    except Exception:
        return []
    return [ln for ln in out.splitlines() if ln.strip()]


def _inner_status_hint(supervisor_tail: str) -> dict:
    """Heuristic: pull recent inner-loop signals from supervisor log."""
    last_spawn = ""
    last_exit = ""
    for ln in supervisor_tail.splitlines():
        if "inner loop spawned" in ln:
            last_spawn = ln
        elif "inner exited" in ln:
            last_exit = ln
    return {"last_inner_spawn_log": last_spawn, "last_inner_exit_log": last_exit}


def collect_snapshot() -> dict:
    server = _server_status()
    state = _state_summary()
    return {
        "ts": _now_iso(),
        "server": server,
        "board_unfinished": _board_unfinished(),
        "state": state,
        "stage2_reject_clusters": _stage2_reject_clusters(),
        "recent_commits": _recent_commits(),
        "supervisor_tail": _read_tail(SUPERVISOR_LOG, n=30),
        "inner_hints": _inner_status_hint(_read_tail(SUPERVISOR_LOG, n=80)),
    }


def _hash_concern(concern: str) -> str:
    canon = re.sub(r"\s+", " ", concern.strip().lower())[:300]
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()[:16]


def _load_concern_counts() -> dict:
    if not CONCERN_COUNTS_PATH.exists():
        return {}
    try:
        return json.loads(CONCERN_COUNTS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _save_concern_counts(counts: dict) -> None:
    CONCERN_COUNTS_PATH.parent.mkdir(parents=True, exist_ok=True)
    CONCERN_COUNTS_PATH.write_text(
        json.dumps(counts, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def bump_concerns(concerns: list[str]) -> list[dict]:
    """Increment counters for each concern; return entries that crossed
    ESCALATE_AFTER_REPEATS for the first time."""
    counts = _load_concern_counts()
    escalated: list[dict] = []
    seen_keys: set[str] = set()
    for concern in concerns:
        if not concern or not concern.strip():
            continue
        key = _hash_concern(concern)
        if key in seen_keys:
            continue
        seen_keys.add(key)
        entry = counts.get(key, {"text": concern.strip(), "count": 0, "first_seen": _now_iso(), "last_seen": _now_iso(), "escalated": False})
        prev = entry.get("count", 0)
        entry["count"] = prev + 1
        entry["text"] = concern.strip()
        entry["last_seen"] = _now_iso()
        if entry["count"] >= ESCALATE_AFTER_REPEATS and not entry.get("escalated"):
            entry["escalated"] = True
            entry["escalated_at"] = _now_iso()
            escalated.append({"hash": key, **entry})
        counts[key] = entry
    _save_concern_counts(counts)
    return escalated


def append_human_inbox(items: list[str]) -> None:
    if not items:
        return
    HUMAN_INBOX.parent.mkdir(parents=True, exist_ok=True)
    block = "\n## " + _now_iso() + "\n\n" + "\n".join(f"- {it}" for it in items) + "\n"
    with open(HUMAN_INBOX, "a", encoding="utf-8") as f:
        f.write(block)


def journal(entry: dict) -> None:
    PI_JOURNAL.parent.mkdir(parents=True, exist_ok=True)
    with open(PI_JOURNAL, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


# ---------------------------------------------------------------------------
# Action executors (whitelist; supervisor passes its own context for
# adjustments that affect supervisor-private cooldowns)
# ---------------------------------------------------------------------------


ALLOWED_AUTONOMOUS = {"run_probe", "run_curator", "restart_inner", "adjust_cooldown"}
ALLOWED_INBOX = {"cancel_target", "adjust_parallel", "prompt_repair", "prune_board", "other"}


def _run_probe_subprocess() -> None:
    auto_discovery = SCRIPT_DIR / "auto_discovery.py"
    subprocess.Popen(
        ["python3", str(auto_discovery), "probe", "--append"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _run_curator_subprocess() -> None:
    auto_discovery = SCRIPT_DIR / "auto_discovery.py"
    subprocess.Popen(
        ["python3", str(auto_discovery), "curator", "--append"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def apply_actions(plan: dict, supervisor_callbacks: dict | None = None) -> list[str]:
    """Apply autonomous actions; return list of action descriptions actually applied."""
    applied: list[str] = []
    callbacks = supervisor_callbacks or {}
    for entry in plan.get("autonomous_actions") or []:
        action = (entry.get("action") or "").strip()
        if action not in ALLOWED_AUTONOMOUS:
            applied.append(f"REJECT (not in allowlist): {action}")
            continue
        args = entry.get("args") or {}
        try:
            if action == "run_probe":
                _run_probe_subprocess()
                applied.append("run_probe")
            elif action == "run_curator":
                _run_curator_subprocess()
                applied.append("run_curator")
            elif action == "restart_inner":
                cb = callbacks.get("restart_inner")
                if cb:
                    cb()
                    applied.append("restart_inner")
                else:
                    applied.append("SKIP restart_inner: no supervisor callback")
            elif action == "adjust_cooldown":
                cb = callbacks.get("adjust_cooldown")
                if cb:
                    cb(args)
                    applied.append(f"adjust_cooldown {args}")
                else:
                    applied.append(f"SKIP adjust_cooldown: no supervisor callback")
        except Exception as exc:
            applied.append(f"ERROR applying {action}: {exc}")
    return applied


def stage_inbox_items(plan: dict, escalated_concerns: list[dict]) -> list[str]:
    """Format human-inbox items from plan + escalated concerns."""
    items: list[str] = []
    for entry in plan.get("human_inbox") or []:
        action = (entry.get("action") or "").strip()
        details = (entry.get("details") or "").strip()
        if action not in ALLOWED_INBOX:
            continue
        items.append(f"**{action}** — {details}")
    for c in escalated_concerns:
        items.append(f"**recurring concern** (seen {c.get('count')}× since {c.get('first_seen','?')}): {c.get('text','')[:300]}")
    return items


# ---------------------------------------------------------------------------
# entry: run_review (called by supervisor)
# ---------------------------------------------------------------------------


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
        if first == -1 or last == -1:
            return None
        candidate = text[first:last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


def run_review(supervisor_callbacks: dict | None = None) -> dict | None:
    """Single PI cycle. Returns the parsed plan (may be None on failure)."""
    from killo_golden_writeback import claude_exec
    snapshot = collect_snapshot()
    template = PROMPT_PATH.read_text(encoding="utf-8")
    snapshot_json = json.dumps(snapshot, ensure_ascii=False, indent=2)
    prompt = template.format(snapshot=_safe(snapshot_json[:30000]))
    ok, stdout, rc = claude_exec(prompt, timeout=PI_TIMEOUT_S, log_tag="pi_review")
    plan: dict | None = None
    if ok:
        plan = _extract_json_object(stdout)

    applied: list[str] = []
    inbox: list[str] = []
    escalated: list[dict] = []
    if plan:
        escalated = bump_concerns(plan.get("concerns") or [])
        applied = apply_actions(plan, supervisor_callbacks=supervisor_callbacks)
        inbox = stage_inbox_items(plan, escalated)
        if inbox:
            append_human_inbox(inbox)

    journal({
        "ts": _now_iso(),
        "ok": ok,
        "rc": rc,
        "snapshot": snapshot,
        "plan": plan,
        "applied": applied,
        "escalated_concerns": escalated,
        "inbox_items_appended": inbox,
        "claude_stdout_truncated": (stdout or "")[:8000],
    })
    return plan


def main() -> int:
    """Standalone CLI for running the PI agent without supervisor (dry-run)."""
    plan = run_review()
    if plan is None:
        print("(no plan parsed; see state/pi_journal.jsonl)", file=sys.stderr)
        return 1
    print(json.dumps(plan, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""PI agent v1 — maker/checker gauntlet over an expanded action surface.

v0 (`pi_agent.py`) was a "look but don't touch" observer with a tiny
allowlist (run_probe / run_curator / restart_inner / adjust_cooldown).
v1 widens the surface significantly and gates every non-routine action
through a two-stage judge:

    PI agent (claude) proposes plan
        ↓
    For each proposed action:
        ├─ codex_evaluator  scores 0-10 across 4 dimensions
        ├─ redline_check    deterministic Python: file paths, operation
        │                   type, branch identity (must be
        │                   bedc-claim-packet-pipeline)
        └─ claude_judge     independent second opinion
        ↓
    Action executes iff all three pass

Redlines are HARD:
- only edits within tools/bedc-deep/
- never touches lean4/, papers/bedc/parts/, .github/, lakefile.lean,
  papers/bedc/preamble.tex, papers/bedc/Makefile
- only on branch bedc-claim-packet-pipeline
- only commit + sync + push (no PR, no merge to other branches, no force-push)

Reuses pi_agent.py's snapshot helpers, concern bumping, and human_inbox
plumbing — only the action surface and the gauntlet are new.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# Shared helpers (formerly in pi_agent.py / v0; v0 retired in favour of v1).
from pi_common import (
    SCRIPT_DIR,
    REPO_ROOT,
    SUPERVISOR_LOG,
    HUMAN_INBOX,
    PI_TIMEOUT_S,
    bump_concerns,
    append_human_inbox,
    journal,
    collect_snapshot as collect_snapshot_v0,
)


PROMPTS_DIR = SCRIPT_DIR / "prompts"
PI_V1_PROMPT_PATH = PROMPTS_DIR / "pi_agent_v1.txt"
PI_CODEX_EVAL_PROMPT_PATH = PROMPTS_DIR / "pi_action_codex_evaluator.txt"
PI_CLAUDE_JUDGE_PROMPT_PATH = PROMPTS_DIR / "pi_action_claude_judge.txt"

LOG_DIR = SCRIPT_DIR / "state" / "pi_v1_logs"
RECENT_CYCLES_PATH = SCRIPT_DIR / "state" / "pi_recent_cycles.jsonl"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

# Hard redlines
ALLOWED_BRANCH = "bedc-claim-packet-pipeline"
WRITE_PATH_PREFIX = REPO_ROOT / "tools" / "bedc-deep"
PROMPT_PATH_PREFIX = REPO_ROOT / "tools" / "bedc-deep" / "prompts"

# Action classification
ROUTINE_ACTIONS = {
    "run_probe", "run_curator", "restart_inner", "adjust_cooldown",
    "git_commit", "git_push", "git_sync_dev",
}
OPERATIONAL_ACTIONS = {
    "cancel_target", "reset_target", "adjust_parallel", "prune_board",
}
HOT_ACTIONS = {
    "edit_prompt", "edit_pipeline_code",
}
ALL_ACTIONS = ROUTINE_ACTIONS | OPERATIONAL_ACTIONS | HOT_ACTIONS

# Files PI v1 may NOT touch even within tools/bedc-deep
PROTECTED_FILES = {
    "supervisor.py",      # too central; must propose in human_inbox
    "oracle_client.py",   # too central; must propose in human_inbox
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _extract_json_object(text: str) -> Optional[dict]:
    """Robust JSON extractor (same scanner as codex_track / board_spawn)."""
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    for start in range(len(text)):
        if text[start] != "{":
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(text)):
            ch = text[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    candidate = text[start : i + 1]
                    try:
                        return json.loads(candidate)
                    except json.JSONDecodeError:
                        break
    return None


def _claude_exec(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    (LOG_DIR / f"{log_tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, cwd=str(REPO_ROOT), env=env, encoding="utf-8", errors="replace",
        start_new_session=True,
    )
    stdout = ""; stderr = ""; rc = -1
    hard_killed = {"flag": False}
    def _hard_kill() -> None:
        hard_killed["flag"] = True
        try: os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError): pass
    watchdog = threading.Timer(timeout + 60, _hard_kill); watchdog.daemon = True; watchdog.start()
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid, 9)
        except ProcessLookupError: pass
        try: stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""; stderr = stderr or ""
        rc = -9
    finally:
        watchdog.cancel()
    if hard_killed["flag"] and rc == 0:
        rc = -9
    (LOG_DIR / f"{log_tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (LOG_DIR / f"{log_tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)


def _codex_exec(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    """Mirrors codex_orchestrator.codex_exec but lives here to avoid a circular
    dependency. Same hard-kill watchdog."""
    if not CODEX_PATH or not Path(CODEX_PATH).exists():
        return (False, f"codex CLI not found at {CODEX_PATH}", -1)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    prompt_file = LOG_DIR / f"{log_tag}_{ts}.prompt.txt"
    output_file = LOG_DIR / f"{log_tag}_{ts}.out.txt"
    prompt_file.write_text(prompt, encoding="utf-8")
    cmd = [CODEX_PATH, "exec", "--sandbox", "read-only", "--json",
           "-C", str(REPO_ROOT), "-o", str(output_file), "-"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, cwd=str(REPO_ROOT), env=env, encoding="utf-8", errors="replace",
        start_new_session=True,
    )
    stdout = ""; stderr = ""; rc = -1
    hard_killed = {"flag": False}
    def _hard_kill() -> None:
        hard_killed["flag"] = True
        try: os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError): pass
    watchdog = threading.Timer(timeout + 60, _hard_kill); watchdog.daemon = True; watchdog.start()
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid, 9)
        except ProcessLookupError: pass
        try: stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""; stderr = stderr or ""
        rc = -9
    finally:
        watchdog.cancel()
    if hard_killed["flag"] and rc == 0:
        rc = -9
    raw = ""
    if output_file.exists() and output_file.stat().st_size > 0:
        raw = output_file.read_text(encoding="utf-8", errors="replace")
    if not raw:
        raw = stdout
    return (rc == 0, raw, rc)


# ---------------------------------------------------------------------------
# Snapshot enrichment (v1 adds completion rate, codex/oracle accept rates,
# prompt file mtimes, recent PI cycles)
# ---------------------------------------------------------------------------


def collect_snapshot_v1() -> dict:
    base = collect_snapshot_v0()
    base["pipeline_version_target"] = "v2"  # what v1 expects to manage
    base["completion_rates"] = _completion_rates()
    base["codex_track_summary"] = _codex_track_summary()
    base["prompt_files"] = _prompt_files_inventory()
    base["recent_pi_cycles"] = _read_recent_cycles(n=10)
    base["current_branch"] = _current_branch()
    return base


def _completion_rates() -> dict:
    """Targets/hour over last 1h, 6h, 24h based on commit timestamps."""
    rates: dict[str, float] = {}
    try:
        # paper writeback batch commits as proxy
        log = subprocess.run(
            ["git", "log", "--since", "24 hours ago",
             "--grep", "paper writeback batch", "--format=%ct"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=10,
        ).stdout
        epochs = [int(x) for x in log.splitlines() if x.strip().isdigit()]
    except Exception:
        epochs = []
    now = int(time.time())
    for label, hours in (("1h", 1), ("6h", 6), ("24h", 24)):
        cutoff = now - hours * 3600
        n = sum(1 for e in epochs if e >= cutoff)
        rates[label] = round(n / hours, 2)
    return rates


def _codex_track_summary() -> dict:
    """Aggregate codex_close_path rate from final state files."""
    state_dir = SCRIPT_DIR / "state"
    if not state_dir.exists():
        return {}
    total = 0; codex_close = 0; oracle_path = 0
    for f in state_dir.glob("*.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if d.get("pipeline_version") != "v2":
            continue
        total += 1
        if d.get("codex_close_path"):
            codex_close += 1
        else:
            oracle_path += 1
    return {
        "v2_total": total,
        "codex_close": codex_close,
        "oracle_path": oracle_path,
        "codex_close_rate": round(codex_close / total, 2) if total else None,
    }


def _prompt_files_inventory() -> list[dict]:
    out = []
    if not PROMPT_PATH_PREFIX.exists():
        return out
    for p in sorted(PROMPT_PATH_PREFIX.glob("*.txt")):
        try:
            st = p.stat()
        except OSError:
            continue
        out.append({
            "path": str(p.relative_to(REPO_ROOT)),
            "size": st.st_size,
            "mtime": datetime.fromtimestamp(st.st_mtime).isoformat(timespec="seconds"),
        })
    return out


def _read_recent_cycles(n: int = 10) -> list[dict]:
    if not RECENT_CYCLES_PATH.exists():
        return []
    try:
        lines = RECENT_CYCLES_PATH.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    out = []
    for line in lines[-n:]:
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return out


def _append_recent_cycle(record: dict) -> None:
    RECENT_CYCLES_PATH.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(record, ensure_ascii=False)
    with RECENT_CYCLES_PATH.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def _current_branch() -> str:
    try:
        return subprocess.run(
            ["git", "branch", "--show-current"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=5,
        ).stdout.strip()
    except Exception:
        return "?"


# ---------------------------------------------------------------------------
# Redline check (deterministic, never calls LLM)
# ---------------------------------------------------------------------------


@dataclass
class RedlineResult:
    passed: bool
    failures: list[str] = field(default_factory=list)


def _redline_check(action: dict) -> RedlineResult:
    failures: list[str] = []

    # Branch identity
    branch = _current_branch()
    if branch != ALLOWED_BRANCH:
        failures.append(
            f"branch {branch!r} != allowed branch {ALLOWED_BRANCH!r}; abort"
        )

    name = (action.get("action") or "").strip()
    if name not in ALL_ACTIONS:
        failures.append(f"action {name!r} not in allowlist {sorted(ALL_ACTIONS)}")

    args = action.get("args") or {}

    # Path-bearing actions: must be inside tools/bedc-deep/
    if name in ("edit_prompt", "edit_pipeline_code"):
        path_str = str(args.get("path", "")).strip()
        if not path_str:
            failures.append("missing path arg")
        else:
            try:
                resolved = (REPO_ROOT / path_str).resolve()
                resolved.relative_to(WRITE_PATH_PREFIX)
            except (ValueError, OSError):
                failures.append(f"path {path_str!r} outside {WRITE_PATH_PREFIX}")
            else:
                if name == "edit_prompt":
                    if not str(resolved).endswith(".txt"):
                        failures.append(f"edit_prompt path must end in .txt: {path_str}")
                    try:
                        resolved.relative_to(PROMPT_PATH_PREFIX)
                    except ValueError:
                        failures.append(f"edit_prompt path must be in prompts/: {path_str}")
                if name == "edit_pipeline_code":
                    if not str(resolved).endswith(".py"):
                        failures.append(f"edit_pipeline_code path must end in .py: {path_str}")
                    if resolved.name in PROTECTED_FILES:
                        failures.append(
                            f"edit_pipeline_code path is protected (use human_inbox): {resolved.name}"
                        )
            # diff must be present
            if not args.get("diff", "").strip():
                failures.append("missing diff arg")
            if not args.get("patch_description", "").strip():
                failures.append("missing patch_description arg")

    # Cancel/reset target: target_id must look right
    if name in ("cancel_target", "reset_target"):
        tid = str(args.get("target_id", "")).strip()
        if not re.match(r"^B-\d{2,3}$", tid):
            failures.append(f"target_id {tid!r} doesn't match B-XX pattern")

    # Prune board: target_ids list
    if name == "prune_board":
        tids = args.get("target_ids") or []
        if not isinstance(tids, list) or not tids:
            failures.append("prune_board needs non-empty target_ids list")
        else:
            for tid in tids:
                if not re.match(r"^B-\d{2,3}$", str(tid).strip()):
                    failures.append(f"prune_board target_id {tid!r} bad form")

    return RedlineResult(passed=not failures, failures=failures)


# ---------------------------------------------------------------------------
# Maker/checker gauntlet
# ---------------------------------------------------------------------------


@dataclass
class GauntletResult:
    pass_all: bool
    codex: dict = field(default_factory=dict)
    redline: dict = field(default_factory=dict)
    claude: dict = field(default_factory=dict)
    summary: str = ""


def _run_codex_evaluator(*, action: dict, snapshot: dict, pi_rationale: str) -> dict:
    template = PI_CODEX_EVAL_PROMPT_PATH.read_text(encoding="utf-8")
    snapshot_blob = json.dumps(snapshot, ensure_ascii=False, indent=2)[:20000]
    prompt = template.format(
        snapshot=_safe(snapshot_blob),
        action=_safe(json.dumps(action, ensure_ascii=False, indent=2)),
        pi_rationale=_safe(pi_rationale[:2000]),
    )
    ok, raw, _rc = _codex_exec(prompt, timeout=300, log_tag=f"pi_codex_eval_{action.get('action','x')}")
    if not ok:
        return {"approve": False, "rationale": "codex unreachable", "raw": raw[:500]}
    parsed = _extract_json_object(raw)
    if not parsed:
        return {"approve": False, "rationale": "codex output not JSON", "raw": raw[:500]}
    return parsed


def _run_claude_judge(*, action: dict, snapshot: dict, pi_rationale: str,
                     codex_verdict: dict, redline_verdict: dict) -> dict:
    template = PI_CLAUDE_JUDGE_PROMPT_PATH.read_text(encoding="utf-8")
    snapshot_blob = json.dumps(snapshot, ensure_ascii=False, indent=2)[:20000]
    prompt = template.format(
        snapshot=_safe(snapshot_blob),
        action=_safe(json.dumps(action, ensure_ascii=False, indent=2)),
        pi_rationale=_safe(pi_rationale[:2000]),
        codex_verdict=_safe(json.dumps(codex_verdict, ensure_ascii=False, indent=2)[:5000]),
        redline_verdict=_safe(json.dumps(redline_verdict, ensure_ascii=False, indent=2)[:2000]),
    )
    ok, stdout, _rc = _claude_exec(prompt, timeout=300, log_tag=f"pi_claude_judge_{action.get('action','x')}")
    if not ok:
        return {"approve": False, "rationale": "claude judge unreachable", "raw": stdout[:500]}
    parsed = _extract_json_object(stdout)
    if not parsed:
        return {"approve": False, "rationale": "claude judge output not JSON", "raw": stdout[:500]}
    return parsed


def gauntlet(action: dict, snapshot: dict, pi_rationale: str) -> GauntletResult:
    """Run the three-stage gauntlet on a single action."""
    redline = _redline_check(action)
    redline_dict = {"passed": redline.passed, "failures": redline.failures}
    if not redline.passed:
        return GauntletResult(
            pass_all=False, redline=redline_dict,
            summary=f"redline failed: {'; '.join(redline.failures)}",
        )
    # Routine actions skip codex/claude (their gauntlet would be overkill)
    name = (action.get("action") or "").strip()
    if name in ROUTINE_ACTIONS:
        return GauntletResult(
            pass_all=True, redline=redline_dict,
            summary="routine action; redline-only gate",
        )

    codex = _run_codex_evaluator(action=action, snapshot=snapshot, pi_rationale=pi_rationale)
    if not codex.get("approve"):
        return GauntletResult(
            pass_all=False, redline=redline_dict, codex=codex,
            summary=f"codex rejected: {codex.get('rationale','')[:200]}",
        )
    claude = _run_claude_judge(
        action=action, snapshot=snapshot, pi_rationale=pi_rationale,
        codex_verdict=codex, redline_verdict=redline_dict,
    )
    if not claude.get("approve"):
        return GauntletResult(
            pass_all=False, redline=redline_dict, codex=codex, claude=claude,
            summary=f"claude rejected: {claude.get('rationale','')[:200]}",
        )
    return GauntletResult(
        pass_all=True, redline=redline_dict, codex=codex, claude=claude,
        summary="gauntlet pass (3/3)",
    )


# ---------------------------------------------------------------------------
# Action executors (only called after gauntlet passes)
# ---------------------------------------------------------------------------


def _exec_cancel_target(args: dict) -> str:
    tid = str(args.get("target_id", "")).strip()
    reason = str(args.get("reason", ""))[:200]
    state_dir = SCRIPT_DIR / "state"
    matches = [d for d in state_dir.iterdir() if d.is_dir() and d.name.startswith(tid.lower() + "_")]
    if not matches:
        return f"cancel_target {tid}: no matching state dir"
    slug = matches[0].name
    in_progress = state_dir / slug / ".in_progress"
    if in_progress.exists():
        # Refuse to cancel an active worker — the worker would otherwise
        # finish its run and overwrite our cancel state. Symmetric with
        # _exec_reset_target. The right path is human_inbox if a target
        # truly needs killing mid-flight.
        return (
            f"cancel_target {tid}: REFUSED — in_progress claim active "
            f"({in_progress.read_text(encoding='utf-8').strip()}). "
            f"Use human_inbox `cancel_target` instead so a human can stop "
            f"the worker first."
        )
    final_state_path = state_dir / f"{slug}.json"
    state = {
        "target_id": tid,
        "stage1_verdict": "cancelled",
        "completed_at": _now_iso(),
        "cancelled_by": "pi_agent_v1",
        "cancel_reason": reason,
        "failure_kind": "cancelled",
        "next_action": "skip",
        "retry_budget": 0,
    }
    final_state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
    return f"cancel_target {tid}: in_progress cleared, final state written"


def _exec_reset_target(args: dict) -> str:
    tid = str(args.get("target_id", "")).strip()
    state_dir = SCRIPT_DIR / "state"
    matches = [d for d in state_dir.iterdir() if d.is_dir() and d.name.startswith(tid.lower() + "_")]
    if not matches:
        return f"reset_target {tid}: no matching state dir"
    slug = matches[0].name
    in_progress = state_dir / slug / ".in_progress"
    if in_progress.exists():
        return f"reset_target {tid}: in_progress claim active, refusing"
    final_state_path = state_dir / f"{slug}.json"
    if final_state_path.exists():
        final_state_path.unlink()
    cursor_dir = state_dir / slug
    if cursor_dir.exists():
        shutil.rmtree(cursor_dir, ignore_errors=True)
    transcript_dir = SCRIPT_DIR / "targets" / slug
    if transcript_dir.exists():
        shutil.rmtree(transcript_dir, ignore_errors=True)
    return f"reset_target {tid}: state + cursor + transcript cleared"


def _exec_edit_prompt(args: dict) -> str:
    path_str = str(args.get("path", "")).strip()
    diff_text = str(args.get("diff", ""))
    target = (REPO_ROOT / path_str).resolve()
    target.relative_to(PROMPT_PATH_PREFIX)  # already redline-checked
    rc = _apply_unified_diff(target, diff_text)
    if rc != 0:
        return f"edit_prompt {path_str}: patch failed rc={rc}"
    return f"edit_prompt {path_str}: applied"


def _exec_edit_pipeline_code(args: dict) -> str:
    path_str = str(args.get("path", "")).strip()
    diff_text = str(args.get("diff", ""))
    target = (REPO_ROOT / path_str).resolve()
    target.relative_to(WRITE_PATH_PREFIX)
    rc = _apply_unified_diff(target, diff_text)
    if rc != 0:
        return f"edit_pipeline_code {path_str}: patch failed rc={rc}"
    return f"edit_pipeline_code {path_str}: applied"


def _apply_unified_diff(target: Path, diff_text: str) -> int:
    """Apply a unified diff via `patch`. Returns 0 on success."""
    if not diff_text.strip():
        return 1
    proc = subprocess.run(
        ["patch", "-p0", str(target)],
        input=diff_text, text=True, capture_output=True, cwd=str(REPO_ROOT), timeout=30,
    )
    return proc.returncode


def _exec_git_commit() -> str:
    """Commit pipeline-owned dirty files. Holds paper_writes lock to avoid
    racing with a concurrent Stage 2 append + make."""
    from locks import file_lock
    with file_lock("paper_writes"):
        sub = subprocess.run(
            ["git", "status", "--porcelain"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=10,
        )
        files = []
        for line in sub.stdout.splitlines():
            p = line[3:].strip()
            if p.startswith(("tools/bedc-deep/", "papers/bedc/parts/")):
                files.append(p)
        if not files:
            return "git_commit: nothing to commit"
        subprocess.run(["git", "add", *files], cwd=str(REPO_ROOT), check=False, timeout=30)
        msg = f"pi_agent_v1: pipeline housekeeping at {_now_iso()}"
        proc = subprocess.run(
            ["git", "commit", "-m", msg], cwd=str(REPO_ROOT),
            capture_output=True, text=True, timeout=30,
        )
        if proc.returncode != 0:
            return f"git_commit: rc={proc.returncode} {proc.stderr[:200]}"
        return f"git_commit: committed {len(files)} files"


def _exec_git_push() -> str:
    """Push to origin. Holds paper_writes lock so an in-progress Stage 2
    append doesn't end up in a partially-committed remote state."""
    from locks import file_lock
    branch = _current_branch()
    if branch != ALLOWED_BRANCH:
        return f"git_push: branch {branch!r} != {ALLOWED_BRANCH!r}; refused"
    with file_lock("paper_writes"):
        proc = subprocess.run(
            ["git", "push", "origin", branch], cwd=str(REPO_ROOT),
            capture_output=True, text=True, timeout=60,
        )
        if proc.returncode != 0:
            return f"git_push: rc={proc.returncode} {proc.stderr[:200]}"
        return f"git_push: pushed {branch}"


def _exec_git_sync_dev() -> str:
    """Fast-forward merge origin/dev. Holds paper_writes lock to prevent
    a Stage 2 append from racing with the merge."""
    from locks import file_lock
    with file_lock("paper_writes"):
        sub = subprocess.run(
            ["git", "status", "--porcelain"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=10,
        )
        if sub.stdout.strip():
            return "git_sync_dev: working tree dirty; refused"
        subprocess.run(["git", "fetch", "origin", "dev"], cwd=str(REPO_ROOT), timeout=30)
        behind = subprocess.run(
            ["git", "rev-list", "--count", "HEAD..origin/dev"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=10,
        ).stdout.strip()
        if behind in ("0", ""):
            return "git_sync_dev: already up to date"
        proc = subprocess.run(
            ["git", "merge", "--no-edit", "origin/dev"], cwd=str(REPO_ROOT),
            capture_output=True, text=True, timeout=60,
        )
        if proc.returncode != 0:
            subprocess.run(["git", "merge", "--abort"], cwd=str(REPO_ROOT), timeout=10)
            return f"git_sync_dev: merge conflict; aborted ({behind} commits)"
        return f"git_sync_dev: merged origin/dev cleanly ({behind} commits)"


def _exec_prune_board(args: dict) -> str:
    """Remove specified BOARD entries (only if no .in_progress claim)."""
    from locks import file_lock
    state_dir = SCRIPT_DIR / "state"
    tids = [str(t).strip() for t in (args.get("target_ids") or [])]
    removed: list[str] = []
    skipped: list[str] = []
    with file_lock("board"):
        text = (SCRIPT_DIR / "BOARD.md").read_text(encoding="utf-8")
        for tid in tids:
            # Don't prune in-flight targets
            in_progress_glob = list(state_dir.glob(f"{tid.lower()}_*/.in_progress"))
            if in_progress_glob:
                skipped.append(f"{tid}: in_progress active")
                continue
            # Remove the section
            pat = rf"\n### {re.escape(tid)} - .+?(?=\n### B-\d|\Z)"
            new_text, n = re.subn(pat, "", text, flags=re.DOTALL)
            if n:
                text = new_text
                removed.append(tid)
            else:
                skipped.append(f"{tid}: not found in BOARD")
        (SCRIPT_DIR / "BOARD.md").write_text(text, encoding="utf-8")
    return f"prune_board: removed={removed} skipped={skipped}"


def _exec_run_probe() -> str:
    auto_discovery = SCRIPT_DIR / "auto_discovery.py"
    subprocess.Popen(
        ["python3", str(auto_discovery), "probe", "--append"],
        cwd=str(REPO_ROOT), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    return "run_probe: spawned"


def _exec_run_curator() -> str:
    auto_discovery = SCRIPT_DIR / "auto_discovery.py"
    subprocess.Popen(
        ["python3", str(auto_discovery), "curator", "--append"],
        cwd=str(REPO_ROOT), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    return "run_curator: spawned"


def _exec_action(action: dict, callbacks: dict) -> str:
    name = (action.get("action") or "").strip()
    args = action.get("args") or {}
    try:
        if name == "run_probe":             return _exec_run_probe()
        if name == "run_curator":           return _exec_run_curator()
        if name == "restart_inner":
            cb = callbacks.get("restart_inner")
            return "restart_inner: " + (cb() if cb else "no callback")
        if name == "adjust_cooldown":
            cb = callbacks.get("adjust_cooldown")
            return "adjust_cooldown: " + (cb(args) if cb else "no callback")
        if name == "git_commit":            return _exec_git_commit()
        if name == "git_push":              return _exec_git_push()
        if name == "git_sync_dev":          return _exec_git_sync_dev()
        if name == "cancel_target":         return _exec_cancel_target(args)
        if name == "reset_target":          return _exec_reset_target(args)
        if name == "adjust_parallel":
            # Cooperative: write intent file; takes effect on next inner respawn
            (SCRIPT_DIR / "state" / ".pi_parallel_intent").write_text(
                str(int(args.get("parallel", 3))), encoding="utf-8",
            )
            return f"adjust_parallel: intent {args.get('parallel')} (effective on next inner respawn)"
        if name == "prune_board":           return _exec_prune_board(args)
        if name == "edit_prompt":           return _exec_edit_prompt(args)
        if name == "edit_pipeline_code":    return _exec_edit_pipeline_code(args)
        return f"unknown action: {name}"
    except Exception as exc:
        return f"ERROR exec {name}: {exc}"


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def run_review(supervisor_callbacks: dict | None = None) -> dict | None:
    """Single PI v1 cycle. Same return semantics as v0.run_review for drop-in."""
    snapshot = collect_snapshot_v1()
    template = PI_V1_PROMPT_PATH.read_text(encoding="utf-8")
    snapshot_blob = json.dumps(snapshot, ensure_ascii=False, indent=2)
    prompt = template.format(snapshot=_safe(snapshot_blob[:30000]))
    ok, stdout, _rc = _claude_exec(prompt, timeout=PI_TIMEOUT_S, log_tag="pi_v1_review")
    plan: dict | None = None
    if ok:
        plan = _extract_json_object(stdout)

    applied: list[dict] = []
    inbox: list[str] = []
    escalated: list[dict] = []
    gauntlet_results: list[dict] = []

    if plan:
        rationale = str(plan.get("rationale", ""))
        escalated = bump_concerns(plan.get("concerns") or [])
        for action in plan.get("autonomous_actions") or []:
            gr = gauntlet(action, snapshot, rationale)
            gauntlet_results.append({
                "action": action,
                "redline": gr.redline,
                "codex_approve": gr.codex.get("approve"),
                "claude_approve": gr.claude.get("approve"),
                "pass_all": gr.pass_all,
                "summary": gr.summary,
            })
            if gr.pass_all:
                outcome = _exec_action(action, supervisor_callbacks or {})
                applied.append({
                    "action": action.get("action"),
                    "args": action.get("args"),
                    "outcome": outcome,
                })
            else:
                # Auto-route blocked autonomous actions to human inbox
                inbox.append(
                    f"**blocked autonomous action** ({action.get('action')}) — {gr.summary}"
                )

        # Manual human_inbox additions from PI agent
        for entry in plan.get("human_inbox") or []:
            inbox.append(
                f"**{entry.get('action','?')}** — {(entry.get('details') or '')[:500]}"
            )
        if escalated:
            for c in escalated:
                inbox.append(
                    f"**recurring concern** (seen {c.get('count')}× since "
                    f"{c.get('first_seen','?')}): {c.get('text','')[:300]}"
                )
        if inbox:
            append_human_inbox(inbox)

    record = {
        "ts": _now_iso(),
        "ok": ok,
        "snapshot_summary": {
            "branch": snapshot.get("current_branch"),
            "completion_rates": snapshot.get("completion_rates"),
            "codex_track_summary": snapshot.get("codex_track_summary"),
        },
        "plan_health": (plan or {}).get("loop_health"),
        "plan_action_count": len((plan or {}).get("autonomous_actions") or []),
        "applied_count": len(applied),
        "inbox_count": len(inbox),
        "escalated_concerns": [c.get("text", "")[:120] for c in escalated],
        "gauntlet_results": gauntlet_results,
    }
    _append_recent_cycle(record)

    journal({
        **record,
        "snapshot": snapshot,
        "plan": plan,
        "applied": applied,
        "inbox_items_appended": inbox,
        "claude_stdout_truncated": (stdout or "")[:8000],
    })
    return plan


def main() -> int:
    """Standalone CLI for dry-run smoke test."""
    import argparse
    parser = argparse.ArgumentParser(description="PI agent v1 standalone cycle")
    parser.add_argument("--dry-run", action="store_true",
                        help="Skip applying any action; just show what gauntlet would have approved.")
    args = parser.parse_args()
    if args.dry_run:
        snapshot = collect_snapshot_v1()
        print(json.dumps({
            "branch": snapshot.get("current_branch"),
            "completion_rates": snapshot.get("completion_rates"),
            "codex_track_summary": snapshot.get("codex_track_summary"),
            "prompt_files_count": len(snapshot.get("prompt_files", [])),
            "recent_pi_cycles_count": len(snapshot.get("recent_pi_cycles", [])),
        }, ensure_ascii=False, indent=2))
        return 0
    plan = run_review()
    print(json.dumps({"plan_present": plan is not None}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""BEDC paper-side Codex revision pipeline with git-worktree parallelism.

Mirror of `lean4/scripts/codex_formalize.py`, but with the two roles swapped
(reviewer + reviser instead of selector + implementor) and with `lake build`
replaced by `make` (pdflatex twice) for verification.

Phases per round (each in its own worktree):
  Phase REVIEW : codex audits the theory in `papers/bedc/parts/` and outputs
                 1–3 concrete revision targets (logical gaps, redundancy,
                 missing companion results, structural improvements, …).
  Gate         : sanity-checks the JSON (count, fields populated, files exist).
  Phase REVISE : codex applies the revisions, runs `make` + `bedc_ci.py audit`,
                 commits the result.
  Phase VERIFY : pipeline-side gates (PDF builds, drift audit, no axioms,
                 no banned vocabulary, ≤800-line .tex cap, no register-only
                 rounds, no new \\leanvariant markers), merge to base, push.

Usage:
  python3 papers/bedc/scripts/codex_revise.py                    # 1 round
  python3 papers/bedc/scripts/codex_revise.py --parallel 3       # 3 parallel
  python3 papers/bedc/scripts/codex_revise.py --parallel 3 --continuous
  python3 papers/bedc/scripts/codex_revise.py --dry-run --parallel 2
  python3 papers/bedc/scripts/codex_revise.py --status
  python3 papers/bedc/scripts/codex_revise.py --cleanup
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED, Future
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
PAPER_ROOT = SCRIPT_DIR.parent              # papers/bedc/
REPO_ROOT = PAPER_ROOT.parent.parent        # newmath/
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "logs"
WORKTREE_DIR = REPO_ROOT / ".worktrees"
PARTS_ROOT = PAPER_ROOT / "parts"

BASE_BRANCH_DEFAULT = "paper-codex-auto-dev"
BASE_BRANCH = BASE_BRANCH_DEFAULT
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

STOP_FILE = REPO_ROOT / ".paper_pipeline.stop"
MAX_TEX_FILE_LINES = 800

# Iteration-narrative vocabulary banned in the paper (CLAUDE.md §写作纪律).
# Detection runs on lines newly added in the round's diff.
FORBIDDEN_VOCAB = [
    "新增", "新版", "修订", "修复了上一版本",
    "增量", "修改记录", "变更记录", "变更原因",
    "patch", "migration", "frozen", "supersede", "superseded",
    "deprecated", "legacy", "increment",
    "rectification", "amendment",
]
# Version-prefixed labels and "v1.5.X"-style numerics
FORBIDDEN_VERSION_RE = re.compile(
    r"\bv\d+\.\d+\.[Xx0-9]+\b|\bv\d+-[A-Za-z0-9_-]+",
)
FORBIDDEN_VOCAB_RE = re.compile(
    r"(" + "|".join(re.escape(w) for w in FORBIDDEN_VOCAB) + r")",
    re.IGNORECASE,
)

# Math syntax: ban LaTeX math environments other than $...$ / $$...$$
FORBIDDEN_MATH_PATTERNS = [
    (r"\\begin\{equation\*?\}", r"\\begin{equation}"),
    (r"\\begin\{align\*?\}",    r"\\begin{align}"),
    (r"\\begin\{eqnarray\*?\}", r"\\begin{eqnarray}"),
    (r"\\\[", r"\\["),
]
FORBIDDEN_MATH_RE = re.compile(
    r"(" + "|".join(p for p, _ in FORBIDDEN_MATH_PATTERNS) + r")"
)

LEAN_MARKER_RE = re.compile(
    r"\\(leanchecked|leanvariant|leanstmt|leandef|leansorryd)\{([^}]+)\}"
)


def _load_prompt(name: str) -> str:
    """Load a prompt template from <SCRIPT_DIR>/prompts/<name>.txt."""
    return (PROMPTS_DIR / f"{name}.txt").read_text(encoding="utf-8")


# Thread-safety primitives
_git_lock = threading.Lock()
_round_lock = threading.Lock()

# In-memory dedup of in-flight target identifiers across parallel rounds.
# We key on (sorted paper_files tuple, anchor) so that two parallel rounds
# do not both try to revise the same theorem block simultaneously.
_active_targets_lock = threading.Lock()
_active_targets: dict[int, set[str]] = {}


def _target_id(t: dict) -> str:
    files = tuple(sorted(t.get("paper_files") or []))
    anchor = (t.get("anchor") or t.get("section_label") or "").strip()
    return f"{'+'.join(files)}::{anchor}"


def claim_targets(round_num: int, targets: list[dict]) -> tuple[list[dict], list[str]]:
    kept: list[dict] = []
    dropped: list[str] = []
    with _active_targets_lock:
        taken: set[str] = set()
        for s in _active_targets.values():
            taken |= s
        keep_ids: set[str] = set()
        for t in targets:
            tid = _target_id(t)
            if not tid.strip("::+"):
                kept.append(t)  # unkeyable; proceed without dedup
                continue
            if tid in taken or tid in keep_ids:
                dropped.append(tid)
                continue
            keep_ids.add(tid)
            kept.append(t)
        if keep_ids:
            _active_targets[round_num] = keep_ids
    return kept, dropped


def release_targets(round_num: int) -> None:
    with _active_targets_lock:
        _active_targets.pop(round_num, None)


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

LOG_DIR.mkdir(parents=True, exist_ok=True)
_log_file = LOG_DIR / f"codex_revise_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(str(_log_file), encoding="utf-8"),
    ],
)
logger = logging.getLogger("codex-revise")


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

@dataclass
class RoundState:
    round_number: int = 0
    consecutive_failures: int = 0
    recent_commits: list[str] = field(default_factory=list)


@dataclass
class ReviewResult:
    raw_output: str = ""
    targets: list[dict] = field(default_factory=list)
    notes: str = ""
    success: bool = False


@dataclass
class ReviseResult:
    raw_output: str = ""
    new_commits: list[str] = field(default_factory=list)
    success: bool = False


@dataclass
class WorktreeInfo:
    path: Path
    branch: str
    round_number: int
    base_sha: str = ""


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------

def run_cmd(
    cmd: list[str],
    *,
    cwd: Optional[Path] = None,
    timeout: int = 120,
    check: bool = False,
) -> subprocess.CompletedProcess:
    logger.debug(f"Running: {' '.join(cmd)}")
    return subprocess.run(
        cmd,
        cwd=str(cwd or REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        stdin=subprocess.DEVNULL,
        check=check,
    )


def git_log_oneline(n: int = 5, *, cwd: Optional[Path] = None) -> list[str]:
    result = run_cmd(["git", "log", "--oneline", f"-{n}"], cwd=cwd or REPO_ROOT)
    return [l.strip() for l in result.stdout.strip().splitlines() if l.strip()]


def latest_committed_round(*, cwd: Optional[Path] = None) -> int:
    result = run_cmd(["git", "log", "--format=%s"], cwd=cwd or REPO_ROOT)
    latest = 0
    for line in result.stdout.splitlines():
        m = re.match(r"P(\d+)\b", line.strip())
        if m:
            latest = max(latest, int(m.group(1)))
    return latest


# ---------------------------------------------------------------------------
# macOS memory-pressure guard (gates dispatch, optional)
# ---------------------------------------------------------------------------

_MEM_GUARD_CFG = {
    "enabled": sys.platform == "darwin",
    "swap_ceiling_gb": 16.0,
    "min_avail_gb": 1.5,
    "poll_seconds": 30,
    "max_wait_seconds": 1800,
}
_mem_guard_lock = threading.Lock()
_SWAP_RE = re.compile(r"used\s*=\s*([\d.]+)([MG])", re.IGNORECASE)


def _macos_swap_used_gb() -> float:
    if sys.platform != "darwin":
        return 0.0
    try:
        r = subprocess.run(
            ["sysctl", "-n", "vm.swapusage"],
            capture_output=True, text=True, timeout=5,
            stdin=subprocess.DEVNULL,
        )
        m = _SWAP_RE.search(r.stdout or "")
        if not m:
            return 0.0
        val = float(m.group(1))
        return val / 1024.0 if m.group(2).upper() == "M" else val
    except Exception:
        return 0.0


def _macos_available_ram_gb() -> float:
    if sys.platform != "darwin":
        return 0.0
    try:
        r = subprocess.run(
            ["vm_stat"], capture_output=True, text=True, timeout=5,
            stdin=subprocess.DEVNULL,
        )
        out = r.stdout or ""
        pm = re.search(r"page size of (\d+) bytes", out)
        page_size = int(pm.group(1)) if pm else 16384
        def _pages(label: str) -> int:
            m = re.search(rf"{re.escape(label)}:\s+(\d+)\.", out)
            return int(m.group(1)) if m else 0
        free_pages = _pages("Pages free") + _pages("Pages inactive") + _pages("Pages speculative")
        return free_pages * page_size / (1024 ** 3)
    except Exception:
        return 0.0


def memory_pressure_wait(context: str = "") -> bool:
    cfg = _MEM_GUARD_CFG
    if not cfg["enabled"]:
        return True
    swap_cap = float(cfg["swap_ceiling_gb"])
    min_avail = float(cfg["min_avail_gb"])
    poll = int(cfg["poll_seconds"])
    max_wait = int(cfg["max_wait_seconds"])

    def _ok(s: float, a: float) -> bool:
        return s < swap_cap or a >= min_avail

    swap, avail = _macos_swap_used_gb(), _macos_available_ram_gb()
    if _ok(swap, avail):
        return True

    with _mem_guard_lock:
        start = time.time()
        warned = False
        while True:
            swap, avail = _macos_swap_used_gb(), _macos_available_ram_gb()
            if _ok(swap, avail):
                if warned:
                    logger.info(
                        f"[mem-guard] cleared (swap={swap:.1f}GB, avail={avail:.1f}GB)"
                        + (f" — resuming {context}" if context else "")
                    )
                return True
            elapsed = int(time.time() - start)
            if elapsed >= max_wait:
                logger.warning(
                    f"[mem-guard] timeout after {elapsed}s "
                    f"(swap={swap:.1f}GB, avail={avail:.1f}GB) — proceeding"
                )
                return False
            logger.warning(
                f"[mem-guard] elevated (swap={swap:.1f}GB, avail={avail:.1f}GB) — "
                f"pausing {context or 'dispatch'} for {poll}s (waited {elapsed}s)"
            )
            warned = True
            time.sleep(poll)


# ---------------------------------------------------------------------------
# Git worktree management
# ---------------------------------------------------------------------------

def ensure_base_branch() -> None:
    with _git_lock:
        result = run_cmd(["git", "branch", "--list", BASE_BRANCH], cwd=REPO_ROOT)
        if BASE_BRANCH not in result.stdout:
            logger.info(f"Creating base branch {BASE_BRANCH} from current HEAD")
            run_cmd(["git", "branch", BASE_BRANCH], cwd=REPO_ROOT, check=True)
            run_cmd(["git", "push", "-u", "origin", BASE_BRANCH], cwd=REPO_ROOT)
            logger.info(f"Base branch {BASE_BRANCH} created")
        else:
            logger.info(f"Base branch {BASE_BRANCH} exists")


def create_worktree(round_num: int) -> WorktreeInfo:
    WORKTREE_DIR.mkdir(parents=True, exist_ok=True)
    branch = f"paper-P{round_num}"
    wt_path = WORKTREE_DIR / f"paper_P{round_num}"
    with _git_lock:
        if wt_path.exists():
            logger.warning(f"Removing stale worktree at {wt_path}")
            run_cmd(["git", "worktree", "remove", "--force", str(wt_path)], cwd=REPO_ROOT)
            if wt_path.exists():
                shutil.rmtree(wt_path, ignore_errors=True)
        run_cmd(["git", "branch", "-D", branch], cwd=REPO_ROOT)
        logger.info(f"Creating worktree: {wt_path} on branch {branch}")
        result = run_cmd(
            ["git", "worktree", "add", "-b", branch, str(wt_path), BASE_BRANCH],
            cwd=REPO_ROOT,
        )
        if result.returncode != 0:
            raise RuntimeError(f"worktree add failed: {result.stderr.strip()}")
    base_sha = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt_path).stdout.strip()
    return WorktreeInfo(path=wt_path, branch=branch,
                        round_number=round_num, base_sha=base_sha)


def remove_worktree(wt: WorktreeInfo) -> None:
    with _git_lock:
        logger.info(f"Removing worktree: {wt.path}")
        run_cmd(["git", "worktree", "remove", "--force", str(wt.path)], cwd=REPO_ROOT)
        if wt.path.exists():
            shutil.rmtree(wt.path, ignore_errors=True)
        run_cmd(["git", "branch", "-D", wt.branch], cwd=REPO_ROOT)


def cleanup_all_worktrees() -> int:
    if not WORKTREE_DIR.exists():
        return 0
    count = 0
    for entry in WORKTREE_DIR.iterdir():
        if entry.is_dir() and entry.name.startswith("paper_P"):
            logger.info(f"Cleaning up {entry}")
            run_cmd(["git", "worktree", "remove", "--force", str(entry)], cwd=REPO_ROOT)
            if entry.exists():
                shutil.rmtree(entry, ignore_errors=True)
            m = re.match(r"paper_P(\d+)", entry.name)
            if m:
                run_cmd(["git", "branch", "-D", f"paper-P{m.group(1)}"], cwd=REPO_ROOT)
            count += 1
    run_cmd(["git", "worktree", "prune"], cwd=REPO_ROOT)
    return count


def _codex_resolve_conflicts(wt_path: Path, *, model: Optional[str] = None,
                             timeout: int = 1200) -> bool:
    status = run_cmd(["git", "diff", "--name-only", "--diff-filter=U"], cwd=wt_path)
    conflicted = [f.strip() for f in status.stdout.splitlines() if f.strip()]
    if not conflicted:
        return True
    logger.info(f"Codex conflict resolution: {len(conflicted)} file(s): {conflicted}")
    prompt = textwrap.dedent(f"""\
        You are resolving git rebase conflicts in the BEDC paper repository.

        Conflicted files: {', '.join(conflicted)}

        ## Resolution rules
        - papers/bedc/parts/**/*.tex: keep both sides' independent edits;
          dedup identical \\leanchecked / \\leanvariant lines; if both sides
          touched the SAME paragraph in incompatible ways, prefer the upstream
          (origin/{BASE_BRANCH}) version.
        - lean4/BEDC.lean and lean4/BEDC/**/*.lean: union all `import` lines,
          dedup; for declaration conflicts, prefer upstream.
        - Do NOT introduce iteration-narrative words (修订/新增/patch/legacy/
          frozen/supersede/deprecated/etc.) when reconciling text.

        After resolving, `git add` each file and `git rebase --continue`. Do
        NOT run `git push`.
    """)
    codex_exec(prompt, work_dir=wt_path, timeout_seconds=timeout, model=model)
    still = run_cmd(["git", "status"], cwd=wt_path)
    if "rebase in progress" in still.stdout.lower():
        logger.warning("Codex did not complete rebase, aborting")
        run_cmd(["git", "rebase", "--abort"], cwd=wt_path)
        return False
    remaining = run_cmd(["git", "diff", "--name-only", "--diff-filter=U"], cwd=wt_path)
    if remaining.stdout.strip():
        logger.warning(f"Codex left unresolved conflicts: {remaining.stdout.strip()}")
        run_cmd(["git", "rebase", "--abort"], cwd=wt_path)
        return False
    return True


def _ff_local_branch_to(target: str) -> tuple[bool, str]:
    """Fast-forward local BASE_BRANCH to `target` (a SHA or revision).

    Works whether or not REPO_ROOT's currently-checked-out branch is
    BASE_BRANCH — earlier versions used `git merge --ff-only` which silently
    advanced the wrong branch when the user's working tree was checked out
    on something else (e.g. `paper-dev`).

    - If REPO_ROOT is on BASE_BRANCH: use `git merge --ff-only` (working tree
      gets the new files).
    - Otherwise: use `git fetch . target:BASE_BRANCH` — a ref-only ff update
      that does not touch any working tree and refuses non-ff (we want that).
    """
    head = run_cmd(["git", "symbolic-ref", "--short", "-q", "HEAD"],
                   cwd=REPO_ROOT, timeout=10)
    current = (head.stdout or "").strip()
    if current == BASE_BRANCH:
        r = run_cmd(["git", "merge", "--ff-only", target],
                    cwd=REPO_ROOT, timeout=30)
    else:
        r = run_cmd(["git", "fetch", ".", f"{target}:{BASE_BRANCH}"],
                    cwd=REPO_ROOT, timeout=30)
    return r.returncode == 0, (r.stderr or r.stdout or "")[-300:]


def merge_worktree_to_base(wt: WorktreeInfo, *, model: Optional[str] = None) -> bool:
    """Rebase the worktree branch onto BASE_BRANCH, ff-update locally, push."""
    with _git_lock:
        logger.info(f"Merging {wt.branch} into {BASE_BRANCH}...")

        def _do(attempt: int) -> bool:
            run_cmd(["git", "fetch", "origin", BASE_BRANCH], cwd=REPO_ROOT, timeout=300)
            # Best-effort ff local BASE_BRANCH from origin. If local has commits
            # origin doesn't (e.g. recovery scenarios), the ff is skipped and
            # we proceed with whatever is local.
            ok, msg = _ff_local_branch_to(f"origin/{BASE_BRANCH}")
            if not ok:
                logger.info(f"local {BASE_BRANCH} ff from origin skipped: {msg.strip()}")
            rebase = run_cmd(["git", "rebase", BASE_BRANCH], cwd=wt.path, timeout=180)
            if rebase.returncode != 0:
                logger.warning(f"Rebase conflict (attempt {attempt}); invoking codex")
                if not _codex_resolve_conflicts(wt.path, model=model):
                    run_cmd(["git", "rebase", "--abort"], cwd=wt.path)
                    return False
            wt_tip = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt.path).stdout.strip()
            ok, msg = _ff_local_branch_to(wt_tip)
            if not ok:
                logger.error(f"ff update of {BASE_BRANCH} failed: {msg.strip()}")
                return False
            push = run_cmd(["git", "push", "origin", BASE_BRANCH],
                           cwd=REPO_ROOT, timeout=300)
            if push.returncode == 0:
                return True
            if attempt == 1:
                logger.warning("Push rejected, retrying")
                return False
            logger.error(f"Push retry failed: {push.stderr[:300]}")
            return False

        if _do(1):
            return True
        return _do(2)


# ---------------------------------------------------------------------------
# Codex CLI invocation
# ---------------------------------------------------------------------------

CODEX_LOG_DIR = LOG_DIR / "codex"


def codex_exec(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 1800,
    output_file: Optional[Path] = None,
    model: Optional[str] = None,
    dry_run: bool = False,
    log_tag: Optional[str] = None,
) -> str:
    if dry_run:
        logger.info(f"[DRY RUN] codex exec (cwd={work_dir}):\n"
                    f"{prompt[:400]}{'...' if len(prompt) > 400 else ''}")
        return "(dry run -- no output)"

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        raise FileNotFoundError("Codex CLI not found")

    target_dir = str(work_dir or REPO_ROOT)
    persist = log_tag is not None
    if persist:
        CODEX_LOG_DIR.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_file = str(CODEX_LOG_DIR / f"{log_tag}_{ts}.prompt.txt")
        with open(prompt_file, "w", encoding="utf-8") as f:
            f.write(prompt)
    else:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", prefix="codex_prompt_",
            delete=False, encoding="utf-8",
        ) as f:
            f.write(prompt)
            prompt_file = f.name

    out_file = str(output_file) if output_file else None
    if out_file is None:
        if persist:
            out_file = str(CODEX_LOG_DIR / f"{log_tag}_{ts}.out.txt")
            open(out_file, "w").close()
        else:
            out_fd, out_file = tempfile.mkstemp(suffix=".txt", prefix="codex_out_")
            os.close(out_fd)

    cmd = [
        "timeout", str(timeout_seconds),
        codex_bin, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C", target_dir,
        "-o", out_file,
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    logger.info(f"Calling codex exec (cwd={target_dir}, timeout={timeout_seconds}s)...")
    start = time.monotonic()
    result = None
    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            result = subprocess.run(
                cmd, stdin=pf, capture_output=True, text=True,
                timeout=timeout_seconds + 30, cwd=target_dir,
            )
    except subprocess.TimeoutExpired:
        logger.warning(f"Codex exec timed out after {timeout_seconds}s")
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        suffix = f" log={log_tag}" if persist else ""
        logger.info(f"Codex exec completed in {elapsed:.1f}s (rc={rc}){suffix}")
        if not persist:
            os.unlink(prompt_file)

    output = ""
    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            output = result.stdout or ""
            if persist and output:
                with open(out_file, "w", encoding="utf-8") as f:
                    f.write(output)
    finally:
        if output_file is None and not persist:
            os.unlink(out_file)
    return output


# ---------------------------------------------------------------------------
# Phase REVIEW (the auditor role)
# ---------------------------------------------------------------------------

def build_review_prompt(round_num: int, recent: str) -> str:
    return (
        _load_prompt("phase_review")
        .replace("<ROUND_NUM>", str(round_num))
        .replace("<RECENT>", recent)
    )


def parse_review_output(raw: str) -> ReviewResult:
    result = ReviewResult(raw_output=raw)
    json_match = re.search(r"```json\s*(\{.*?\})\s*```", raw, re.DOTALL)
    if json_match:
        try:
            data = json.loads(json_match.group(1))
            result.targets = data.get("targets", []) or []
            result.notes = data.get("notes", "") or ""
        except json.JSONDecodeError:
            pass
    if not result.targets:
        for m in re.finditer(r'\{[^{}]*"targets"\s*:\s*\[.*?\]\s*\}', raw, re.DOTALL):
            try:
                data = json.loads(m.group(0))
                result.targets = data.get("targets", []) or []
                if result.targets:
                    break
            except json.JSONDecodeError:
                continue
    # Empty targets is a legitimate outcome ("paper is clean") — distinguish
    # that from "couldn't extract JSON". A successful review either parsed
    # JSON or the raw clearly contained the empty-list signal.
    if result.targets:
        result.success = True
    elif json_match:
        result.success = True  # parsed empty list — paper genuinely clean
    return result


def review_gate_check(review: ReviewResult) -> tuple[bool, str]:
    """Quick sanity check on review JSON. Returns (proceed_to_revise, reason).

    Empty list → do not revise this round (gate FALSE) but it is not a script
    failure — caller logs and moves on.
    """
    if not review.targets:
        return False, "Reviewer reported no high-value targets (empty round)"

    issues: list[str] = []
    for i, t in enumerate(review.targets):
        if not t.get("paper_files"):
            issues.append(f"target {i+1}: missing paper_files")
        if not t.get("proposed_change"):
            issues.append(f"target {i+1}: missing proposed_change")
        if not t.get("summary"):
            issues.append(f"target {i+1}: missing summary")
        # File existence sanity
        for rel in t.get("paper_files") or []:
            if not (REPO_ROOT / rel).exists():
                issues.append(f"target {i+1}: paper_file does not exist: {rel}")
    if issues:
        return False, "; ".join(issues[:6])
    return True, f"{len(review.targets)} target(s) cleared review gate"


# ---------------------------------------------------------------------------
# Phase REVISE (the modifier role)
# ---------------------------------------------------------------------------

def build_revise_prompt(round_num: int, targets: list[dict]) -> str:
    text = ""
    for i, t in enumerate(targets, 1):
        text += (
            f"### Target {i}: {t.get('summary', '(no summary)')}\n"
            f"- kind: {t.get('kind', 'unknown')}\n"
            f"- chapter: {t.get('chapter', 'unknown')}\n"
            f"- difficulty: {t.get('difficulty', 'unknown')}\n"
            f"- paper_files: {', '.join(t.get('paper_files') or [])}\n"
            f"- section_label: {t.get('section_label', '(none)')}\n"
            f"- anchor: {t.get('anchor', '(none)')}\n"
            f"- evidence: {t.get('evidence', '(none)')}\n"
            f"- proposed_change:\n"
            f"{textwrap.indent(t.get('proposed_change', '(none)'), '  ')}\n"
            f"- expected_effect: {t.get('expected_effect', '(none)')}\n"
            f"- lean_touchpoint: {t.get('lean_touchpoint', '(none)')}\n\n"
        )
    return (
        _load_prompt("phase_revise")
        .replace("<ROUND_NUM>", str(round_num))
        .replace("<TARGETS>", text)
        .replace("<BASE_BRANCH>", BASE_BRANCH)
    )


def parse_revise_output(raw: str) -> ReviseResult:
    result = ReviseResult(raw_output=raw)
    commit_hashes = re.findall(r"(?:^|\s)([0-9a-f]{7,12})(?:\s+\w)", raw, re.MULTILINE)
    result.new_commits = list(dict.fromkeys(commit_hashes))[:10]
    indicators = ["make", "git commit", "git add", "pdflatex", "bedc_ci.py"]
    result.success = bool(raw) and any(ind.lower() in raw.lower() for ind in indicators)
    return result


# ---------------------------------------------------------------------------
# Phase VERIFY — pipeline-side gates
# ---------------------------------------------------------------------------

def _changed_files(wt: WorktreeInfo, *, prefix: str = "",
                   diff_filter: str = "AM") -> list[str]:
    if not wt.base_sha:
        return []
    try:
        r = run_cmd(
            ["git", "diff", "--name-only", f"--diff-filter={diff_filter}",
             f"{wt.base_sha}..HEAD", "--", prefix or "."],
            cwd=wt.path,
        )
    except Exception:
        return []
    return [l.strip() for l in (r.stdout or "").splitlines() if l.strip()]


def _changed_tex_files(wt: WorktreeInfo) -> list[str]:
    return [f for f in _changed_files(wt, prefix="papers/bedc/")
            if f.endswith(".tex")]


def _added_lines_per_file(wt: WorktreeInfo, rel_path: str) -> list[tuple[int, str]]:
    """Return (line_no_in_HEAD, content) for each line this round added to rel_path."""
    if not wt.base_sha:
        return []
    try:
        r = run_cmd(
            ["git", "diff", "--unified=0", f"{wt.base_sha}..HEAD", "--", rel_path],
            cwd=wt.path,
        )
    except Exception:
        return []
    out: list[tuple[int, str]] = []
    hunk_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
    current_new: Optional[int] = None
    for line in (r.stdout or "").splitlines():
        m = hunk_re.match(line)
        if m:
            current_new = int(m.group(1))
            continue
        if current_new is None:
            continue
        if line.startswith("+") and not line.startswith("+++"):
            out.append((current_new, line[1:]))
            current_new += 1
        elif line.startswith("-") and not line.startswith("---"):
            pass
        else:
            current_new += 1
    return out


def detect_forbidden_vocab(wt: WorktreeInfo) -> list[str]:
    """Reject diffs that introduce iteration-narrative vocabulary."""
    violations: list[str] = []
    for rel in _changed_files(wt, prefix="papers/bedc/"):
        if not (rel.endswith(".tex") or rel.endswith(".md")):
            continue
        for line_no, content in _added_lines_per_file(wt, rel):
            stripped = content.strip()
            # Skip pure comment lines (% …) — they should not exist either,
            # but the inline-comment ban is a separate gate (out of scope).
            for m in FORBIDDEN_VOCAB_RE.finditer(stripped):
                violations.append(f"{rel}:{line_no}: '{m.group(1)}' — {stripped[:120]}")
                break
            else:
                vm = FORBIDDEN_VERSION_RE.search(stripped)
                if vm:
                    violations.append(
                        f"{rel}:{line_no}: version-prefix '{vm.group(0)}' — {stripped[:120]}"
                    )
    return violations


def detect_forbidden_math(wt: WorktreeInfo) -> list[str]:
    violations: list[str] = []
    for rel in _changed_tex_files(wt):
        for line_no, content in _added_lines_per_file(wt, rel):
            m = FORBIDDEN_MATH_RE.search(content)
            if m:
                violations.append(
                    f"{rel}:{line_no}: forbidden math env '{m.group(1)}' — "
                    f"{content.strip()[:120]}"
                )
    return violations


def detect_oversized_tex(wt: WorktreeInfo) -> list[str]:
    violations: list[str] = []
    for rel in _changed_tex_files(wt):
        try:
            n = len((wt.path / rel).read_text(encoding="utf-8").splitlines())
        except Exception:
            continue
        if n > MAX_TEX_FILE_LINES:
            violations.append(f"{rel}: {n} lines exceeds cap {MAX_TEX_FILE_LINES}")
    return violations


def detect_register_only_round(wt: WorktreeInfo) -> list[str]:
    """A round that only adds \\leanvariant markers (no real .tex content)
    is rejected. A round with zero net non-whitespace changes is rejected."""
    tex_changed = _changed_tex_files(wt)
    lean_changed = [f for f in _changed_files(wt) if f.startswith("lean4/")]
    if not tex_changed and not lean_changed:
        return ["no .tex or .lean files changed in this round"]

    # Detect "only added \leanvariant lines" pattern across paper diff.
    if tex_changed and not lean_changed:
        all_added: list[str] = []
        for rel in tex_changed:
            for _, content in _added_lines_per_file(wt, rel):
                if content.strip():
                    all_added.append(content.strip())
        if all_added and all(LEAN_MARKER_RE.search(l) and "leanvariant" in l
                             for l in all_added):
            return ["round only adds new \\leanvariant markers; not allowed"]
    return []


def detect_new_leanvariant_markers(wt: WorktreeInfo) -> list[str]:
    """Automated rounds must not introduce new \\leanvariant markers."""
    violations: list[str] = []
    for rel in _changed_tex_files(wt):
        for line_no, content in _added_lines_per_file(wt, rel):
            for m in LEAN_MARKER_RE.finditer(content):
                if m.group(1) == "leanvariant":
                    violations.append(
                        f"{rel}:{line_no}: new \\leanvariant{{{m.group(2)}}}"
                    )
    return violations


def run_pdf_build(wt: WorktreeInfo, *, timeout: int = 600) -> tuple[bool, str]:
    """Run `make` in the worktree's papers/bedc directory and return (ok, tail)."""
    paper_dir = wt.path / "papers" / "bedc"
    if not paper_dir.exists():
        return False, "papers/bedc/ missing in worktree"
    log_path = LOG_DIR / f"pdf_build_P{wt.round_number}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
    try:
        with open(log_path, "w", encoding="utf-8") as lf:
            lf.write(f"# make at {datetime.now().isoformat()} cwd={paper_dir}\n\n")
            lf.flush()
            r = subprocess.run(
                ["make"], cwd=str(paper_dir),
                stdout=lf, stderr=subprocess.STDOUT,
                timeout=timeout, stdin=subprocess.DEVNULL,
            )
            ok = r.returncode == 0
    except subprocess.TimeoutExpired:
        return False, f"make timed out after {timeout}s (log={log_path.name})"
    except Exception as exc:
        return False, f"make raised {exc!r}"
    try:
        tail = "\n".join(log_path.read_text(encoding="utf-8").splitlines()[-30:])
    except Exception:
        tail = ""
    return ok, tail


def run_drift_audit(wt: WorktreeInfo) -> tuple[bool, str]:
    audit = wt.path / "lean4" / "scripts" / "bedc_ci.py"
    if not audit.exists():
        return True, "(bedc_ci.py absent — skipping drift audit)"
    try:
        r = run_cmd(["python3", str(audit), "audit"],
                    cwd=wt.path, timeout=180)
    except subprocess.TimeoutExpired:
        return False, "drift audit timed out"
    return r.returncode == 0, (r.stdout + r.stderr)[-800:]


def run_axiom_audit(wt: WorktreeInfo) -> tuple[bool, str]:
    audit = wt.path / "tools" / "check-axioms.py"
    if not audit.exists():
        return True, "(check-axioms.py absent — skipping axiom audit)"
    try:
        r = run_cmd(["python3", str(audit)], cwd=wt.path, timeout=120)
    except subprocess.TimeoutExpired:
        return False, "axiom audit timed out"
    return r.returncode == 0, (r.stdout + r.stderr)[-400:]


def verify_worktree_commits(
    wt: WorktreeInfo, pre_commits: list[str]
) -> tuple[bool, list[str]]:
    """Run all pipeline-side gates. Returns (success, new_commit_oneline_list)."""
    if wt.base_sha:
        result = run_cmd(
            ["git", "log", "--oneline", f"{wt.base_sha}..HEAD"], cwd=wt.path,
        )
        new = [l.strip() for l in result.stdout.splitlines() if l.strip()]
    else:
        post = git_log_oneline(40, cwd=wt.path)
        new = [c for c in post if c not in pre_commits]

    if not new:
        logger.warning(f"[P{wt.round_number}] Verify: no new commits")
        return False, []

    logger.info(f"[P{wt.round_number}] Verify: {len(new)} new commit(s)")
    for c in new:
        logger.info(f"  {c}")

    # Gate A — register-only / nothing-real-changed
    rv = detect_register_only_round(wt)
    if rv:
        for v in rv:
            logger.error(f"[P{wt.round_number}] REGISTER-ONLY: {v}")
        return False, new

    # Gate B — new \leanvariant markers
    var_v = detect_new_leanvariant_markers(wt)
    if var_v:
        for v in var_v[:10]:
            logger.error(f"[P{wt.round_number}] NEW LEANVARIANT: {v}")
        return False, new

    # Gate C — forbidden iteration-narrative vocabulary
    vocab_v = detect_forbidden_vocab(wt)
    if vocab_v:
        for v in vocab_v[:10]:
            logger.error(f"[P{wt.round_number}] FORBIDDEN VOCAB: {v}")
        logger.error(f"[P{wt.round_number}] Rejecting round: iteration-narrative "
                     "vocabulary detected. Replace silently — no version annotations.")
        return False, new

    # Gate D — forbidden math environments
    math_v = detect_forbidden_math(wt)
    if math_v:
        for v in math_v[:10]:
            logger.error(f"[P{wt.round_number}] FORBIDDEN MATH ENV: {v}")
        return False, new

    # Gate E — oversized .tex files
    size_v = detect_oversized_tex(wt)
    if size_v:
        for v in size_v[:10]:
            logger.error(f"[P{wt.round_number}] OVERSIZED .TEX: {v}")
        return False, new

    # Gate F — PDF compile
    ok, tail = run_pdf_build(wt)
    if not ok:
        logger.error(f"[P{wt.round_number}] PDF build FAILED")
        for ln in (tail or "").splitlines()[-15:]:
            logger.error(f"  {ln}")
        return False, new
    logger.info(f"[P{wt.round_number}] PDF build OK")

    # Gate G — paper ↔ Lean drift audit
    ok, msg = run_drift_audit(wt)
    if not ok:
        logger.error(f"[P{wt.round_number}] Drift audit FAILED")
        for ln in msg.splitlines()[-10:]:
            logger.error(f"  {ln}")
        return False, new
    logger.info(f"[P{wt.round_number}] Drift audit OK")

    # Gate H — axiom audit (only if Lean files were touched)
    lean_changed = [f for f in _changed_files(wt) if f.startswith("lean4/")]
    if lean_changed:
        ok, msg = run_axiom_audit(wt)
        if not ok:
            logger.error(f"[P{wt.round_number}] Axiom audit FAILED")
            for ln in msg.splitlines()[-10:]:
                logger.error(f"  {ln}")
            return False, new
        logger.info(f"[P{wt.round_number}] Axiom audit OK")

    return True, new


# ---------------------------------------------------------------------------
# Worktree-based round execution
# ---------------------------------------------------------------------------

def run_round_in_worktree(
    round_num: int,
    recent_commits: list[str],
    *,
    dry_run: bool = False,
    model: Optional[str] = None,
    review_timeout: int = 1200,
    revise_timeout: int = 3600,
) -> tuple[bool, int, list[str]]:
    tag = f"P{round_num}"
    logger.info(f"{'='*60}")
    logger.info(f"[{tag}] Starting paper revision round")
    logger.info(f"{'='*60}")

    wt: Optional[WorktreeInfo] = None
    new_commits: list[str] = []
    success: bool = False
    review = ReviewResult()
    revise = ReviseResult()
    try:
        if not dry_run:
            wt = create_worktree(round_num)
            wt_cwd = wt.path
        else:
            wt_cwd = REPO_ROOT
        pre_commits = git_log_oneline(10, cwd=wt_cwd)
        recent_text = "\n".join(recent_commits[:5]) if recent_commits else "(none)"

        # ── Phase REVIEW ─────────────────────────────────────────
        logger.info(f"[{tag}] Phase REVIEW: theory audit...")
        review_prompt = build_review_prompt(round_num, recent_text)
        review_raw = codex_exec(
            review_prompt,
            work_dir=wt_cwd,
            timeout_seconds=review_timeout,
            model=model,
            dry_run=dry_run,
            log_tag=f"P{round_num}_review",
        )
        review = parse_review_output(review_raw)

        if not review.success:
            logger.error(f"[{tag}] Phase REVIEW failed: could not parse JSON output "
                         f"({len(review.raw_output)} chars)")
            _save_round_log(round_num, review, ReviseResult(), [], False)
            return False, round_num, []

        logger.info(f"[{tag}] Phase REVIEW: {len(review.targets)} target(s)")
        for i, t in enumerate(review.targets, 1):
            logger.info(f"  Target {i}: [{t.get('kind', '?')}/{t.get('difficulty','?')}] "
                        f"{t.get('summary', '')[:100]}")

        # Dedup against in-flight rounds
        kept, dropped = claim_targets(round_num, review.targets)
        if dropped:
            logger.warning(
                f"[{tag}] Dedup: dropping {len(dropped)} target(s) in flight: "
                f"{', '.join(dropped[:3])}{'…' if len(dropped) > 3 else ''}"
            )
        review.targets = kept

        # Review gate
        proceed, reason = review_gate_check(review)
        if not proceed:
            logger.warning(f"[{tag}] Review gate: {reason} — skipping revise phase")
            _save_round_log(round_num, review, ReviseResult(), [], True)
            # Empty round is a benign skip, not a failure.
            return False, round_num, []
        logger.info(f"[{tag}] Review gate: {reason}")

        # ── Phase REVISE ─────────────────────────────────────────
        logger.info(f"[{tag}] Phase REVISE: applying revisions...")
        revise_prompt = build_revise_prompt(round_num, review.targets)
        revise_raw = codex_exec(
            revise_prompt,
            work_dir=wt_cwd,
            timeout_seconds=revise_timeout,
            model=model,
            dry_run=dry_run,
            log_tag=f"P{round_num}_revise",
        )
        revise = parse_revise_output(revise_raw)

        # ── Phase VERIFY ─────────────────────────────────────────
        logger.info(f"[{tag}] Phase VERIFY: gates + PDF build...")
        if dry_run:
            success = True
        else:
            assert wt is not None
            success, new_commits = verify_worktree_commits(wt, pre_commits)

        # ── Merge back ───────────────────────────────────────────
        if success and new_commits and wt and not dry_run:
            logger.info(f"[{tag}] Merging to {BASE_BRANCH}...")
            merged = merge_worktree_to_base(wt, model=model)
            if not merged:
                logger.error(f"[{tag}] Merge failed — keeping worktree for manual fix")
                _save_round_log(round_num, review, revise, new_commits, False)
                return False, round_num, new_commits
            logger.info(f"[{tag}] SUCCESS: merged {len(new_commits)} commit(s)")
        elif success and dry_run:
            logger.info(f"[{tag}] [DRY RUN] Would merge to {BASE_BRANCH}")

        _save_round_log(round_num, review, revise, new_commits, success)
        if success and (new_commits or dry_run):
            logger.info(f"[{tag}] Round SUCCESS")
        else:
            logger.warning(f"[{tag}] Round FAILED")
        return success and bool(new_commits or dry_run), round_num, new_commits

    except Exception as exc:
        logger.error(f"[{tag}] Exception: {exc}", exc_info=True)
        return False, round_num, []
    finally:
        release_targets(round_num)
        if wt and not dry_run:
            try:
                if not new_commits or (success and new_commits):
                    remove_worktree(wt)
            except Exception:
                logger.warning(f"[{tag}] Failed to clean up worktree {wt.path}")


# ---------------------------------------------------------------------------
# State & log persistence
# ---------------------------------------------------------------------------

STATE_FILE = LOG_DIR / "revise_state.json"


def load_state() -> RoundState:
    latest = latest_committed_round()
    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            state = RoundState(**data)
            if latest > state.round_number:
                logger.info(
                    f"Advancing round state from P{state.round_number} to "
                    f"latest commit P{latest}"
                )
                state.round_number = latest
            return state
        except Exception:
            logger.warning("Failed to load state; rebuilding from git")
    return RoundState(
        round_number=latest,
        recent_commits=git_log_oneline(5),
    )


def save_state(state: RoundState) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump({
            "round_number": state.round_number,
            "consecutive_failures": state.consecutive_failures,
            "recent_commits": state.recent_commits[:10],
        }, f, indent=2)


def _save_round_log(
    round_num: int,
    review: ReviewResult,
    revise: ReviseResult,
    new_commits: list[str],
    success: bool,
) -> Path:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = LOG_DIR / f"round_P{round_num}_{ts}.json"
    with open(log_path, "w", encoding="utf-8") as f:
        json.dump({
            "round": round_num,
            "timestamp": ts,
            "success": success,
            "review_targets": review.targets,
            "review_notes": review.notes,
            "review_success": review.success,
            "revise_success": revise.success,
            "new_commits": new_commits,
            "review_output_length": len(review.raw_output),
            "revise_output_length": len(revise.raw_output),
        }, f, indent=2, ensure_ascii=False)
    return log_path


# ---------------------------------------------------------------------------
# Parallel dispatcher
# ---------------------------------------------------------------------------

def allocate_round_numbers(state: RoundState, count: int) -> list[int]:
    with _round_lock:
        base = state.round_number + 1
        nums = list(range(base, base + count))
        state.round_number = base + count - 1
        save_state(state)
        return nums


def run_parallel_batch(
    state: RoundState,
    *,
    parallel: int,
    dry_run: bool = False,
    model: Optional[str] = None,
    review_timeout: int = 1200,
    revise_timeout: int = 3600,
) -> tuple[int, int]:
    nums = allocate_round_numbers(state, parallel)
    recent = state.recent_commits
    logger.info(f"Dispatching batch: P{nums[0]}..P{nums[-1]} ({parallel} workers)")

    succeeded = failed = 0
    with ThreadPoolExecutor(max_workers=parallel, thread_name_prefix="worker") as pool:
        futures: dict[Future, int] = {}
        for rn in nums:
            memory_pressure_wait(context=f"dispatch P{rn}")
            fut = pool.submit(
                run_round_in_worktree,
                rn, recent,
                dry_run=dry_run, model=model,
                review_timeout=review_timeout,
                revise_timeout=revise_timeout,
            )
            futures[fut] = rn
        for fut in as_completed(futures):
            rn = futures[fut]
            try:
                ok, _, commits = fut.result()
                if ok:
                    succeeded += 1
                    logger.info(f"[P{rn}] SUCCESS ({len(commits)} commits)")
                else:
                    failed += 1
                    logger.warning(f"[P{rn}] FAILED")
            except Exception as exc:
                failed += 1
                logger.error(f"[P{rn}] EXCEPTION: {exc}")

    state.recent_commits = git_log_oneline(5)
    if failed == parallel:
        state.consecutive_failures += 1
    else:
        state.consecutive_failures = 0
    save_state(state)
    return succeeded, failed


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    global BASE_BRANCH

    parser = argparse.ArgumentParser(
        description="BEDC paper Codex revision pipeline (review + revise) with worktree parallelism",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              python3 papers/bedc/scripts/codex_revise.py
              python3 papers/bedc/scripts/codex_revise.py --parallel 3
              python3 papers/bedc/scripts/codex_revise.py --parallel 3 --continuous
              python3 papers/bedc/scripts/codex_revise.py --dry-run --parallel 2
              python3 papers/bedc/scripts/codex_revise.py --status
              python3 papers/bedc/scripts/codex_revise.py --cleanup
        """),
    )
    parser.add_argument("--rounds", "-n", type=int, default=1)
    parser.add_argument("--parallel", "-p", type=int, default=1)
    parser.add_argument("--continuous", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--model", "-m", type=str, default=None)
    parser.add_argument("--review-timeout", type=int, default=1200)
    parser.add_argument("--revise-timeout", type=int, default=3600)
    parser.add_argument("--max-consecutive-failures", type=int, default=3)
    parser.add_argument("--reset-state", action="store_true")
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--cleanup", action="store_true")
    parser.add_argument("--stop", action="store_true",
                        help=f"Create {STOP_FILE.name} to drain")
    parser.add_argument("--resume", action="store_true",
                        help=f"Remove {STOP_FILE.name}")
    parser.add_argument("--base-branch", type=str, default=BASE_BRANCH_DEFAULT)
    parser.add_argument("--no-mem-guard", action="store_true",
                        help="Disable macOS memory-pressure dispatch guard")
    args = parser.parse_args()

    BASE_BRANCH = args.base_branch
    if args.no_mem_guard:
        _MEM_GUARD_CFG["enabled"] = False

    if args.cleanup:
        n = cleanup_all_worktrees()
        print(f"Cleaned up {n} worktree(s)")
        return 0

    if args.stop:
        STOP_FILE.touch()
        print(f"Created {STOP_FILE} — pipeline will drain")
        return 0
    if args.resume:
        if STOP_FILE.exists():
            STOP_FILE.unlink()
            print(f"Removed {STOP_FILE} — pipeline will resume")
        else:
            print(f"{STOP_FILE} did not exist")
        return 0

    if args.status:
        state = load_state()
        wt_result = run_cmd(["git", "worktree", "list"], cwd=REPO_ROOT)
        active = [l for l in wt_result.stdout.splitlines() if "paper_P" in l]
        print(f"Round:                 P{state.round_number}")
        print(f"Consecutive failures:  {state.consecutive_failures}")
        print(f"Base branch:           {BASE_BRANCH}")
        print(f"Active worktrees:      {len(active)}")
        for wt in active:
            print(f"  {wt.strip()}")
        print(f"Recent commits:")
        for c in state.recent_commits[:5]:
            print(f"  {c}")
        print(f"Codex CLI:             {CODEX_PATH}")
        print(f"Log dir:               {LOG_DIR}")
        return 0

    if args.reset_state and STATE_FILE.exists():
        STATE_FILE.unlink()
        logger.info("State reset")

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin and not args.dry_run:
        logger.error("Codex CLI not found")
        return 1
    logger.info(f"Codex CLI:    {codex_bin}")
    logger.info(f"Base branch:  {BASE_BRANCH}")
    logger.info(f"Parallelism:  {args.parallel}")

    if not args.dry_run:
        ensure_base_branch()
        run_cmd(["git", "worktree", "prune"], cwd=REPO_ROOT)
        if WORKTREE_DIR.exists():
            for entry in WORKTREE_DIR.iterdir():
                if entry.is_dir() and entry.name.startswith("paper_P"):
                    wt_result = run_cmd(["git", "worktree", "list", "--porcelain"],
                                        cwd=REPO_ROOT)
                    if str(entry) not in wt_result.stdout:
                        logger.info(f"Removing orphaned worktree dir: {entry}")
                        shutil.rmtree(entry, ignore_errors=True)

    state = load_state()
    if state.consecutive_failures:
        logger.info(f"Resetting consecutive_failures={state.consecutive_failures}")
        state.consecutive_failures = 0
        save_state(state)
    logger.info(f"Starting at P{state.round_number}")

    total_succeeded = total_failed = 0

    if args.continuous:
        logger.info(f"{'='*60}")
        logger.info(f"Rolling pipeline: {args.parallel} workers, until stopped")
        logger.info(f"{'='*60}")
        with ThreadPoolExecutor(max_workers=args.parallel,
                                thread_name_prefix="worker") as pool:
            futures: dict[Future, int] = {}
            cooldown_seconds = max(60, int(args.max_consecutive_failures) * 60)

            def _maybe_cooldown() -> None:
                if state.consecutive_failures < args.max_consecutive_failures:
                    return
                logger.warning(f"[cooldown] {state.consecutive_failures} failures — "
                               f"sleeping {cooldown_seconds}s")
                time.sleep(cooldown_seconds)
                state.consecutive_failures = 0
                save_state(state)
                logger.info("[cooldown] resumed")

            def _submit_next() -> None:
                if STOP_FILE.exists():
                    logger.info(f"Stop file detected ({STOP_FILE})")
                    return
                _maybe_cooldown()
                with _round_lock:
                    state.round_number += 1
                    rn = state.round_number
                    save_state(state)
                memory_pressure_wait(context=f"dispatch P{rn}")
                fut = pool.submit(
                    run_round_in_worktree,
                    rn, state.recent_commits,
                    dry_run=args.dry_run, model=args.model,
                    review_timeout=args.review_timeout,
                    revise_timeout=args.revise_timeout,
                )
                futures[fut] = rn
                logger.info(f"Dispatching P{rn} (rolling)")

            for _ in range(args.parallel):
                _submit_next()
            while futures:
                if STOP_FILE.exists():
                    logger.info(f"Stop file detected; draining {len(futures)} workers")
                done, _ = wait(futures, return_when=FIRST_COMPLETED)
                for fut in done:
                    rn = futures.pop(fut)
                    try:
                        ok, _, commits = fut.result()
                        if ok:
                            total_succeeded += 1
                            state.consecutive_failures = 0
                        else:
                            total_failed += 1
                            state.consecutive_failures += 1
                    except Exception as exc:
                        total_failed += 1
                        state.consecutive_failures += 1
                        logger.error(f"[P{rn}] EXCEPTION: {exc}")
                    state.recent_commits = git_log_oneline(5)
                    save_state(state)
                    if not STOP_FILE.exists():
                        _submit_next()
    else:
        for batch_idx in range(args.rounds):
            if state.consecutive_failures >= args.max_consecutive_failures:
                logger.error(f"Stopping: {state.consecutive_failures} consecutive failures")
                break
            logger.info(f"{'='*60}")
            logger.info(f"Batch {batch_idx + 1}: dispatching {args.parallel} worker(s)")
            logger.info(f"{'='*60}")
            s, f = run_parallel_batch(
                state, parallel=args.parallel, dry_run=args.dry_run,
                model=args.model, review_timeout=args.review_timeout,
                revise_timeout=args.revise_timeout,
            )
            total_succeeded += s
            total_failed += f
            logger.info(f"Batch {batch_idx + 1}: {s} succeeded, {f} failed")
            if batch_idx < args.rounds - 1 and not args.dry_run:
                time.sleep(5)

    logger.info(f"{'='*60}")
    logger.info(f"Session complete: {total_succeeded} succeeded, {total_failed} failed")
    logger.info(f"Final round: P{state.round_number}")
    logger.info(f"{'='*60}")
    return 0 if total_succeeded > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())

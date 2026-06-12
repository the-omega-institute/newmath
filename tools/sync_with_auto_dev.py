#!/usr/bin/env python3
"""Managed rollup PR from a source branch into a target branch.

Default flow:
  1. fetch origin
  2. create an isolated worktree from `origin/dev`
  3. merge `origin/codex-auto-dev` with `git merge --no-ff --no-edit`
  4. resolve conflicts through codex when needed
  5. regenerate `lean4/BEDC.lean`
  6. push a managed rollup branch and maintain one PR into the target branch

The source and target branches are configurable. The default is
`codex-auto-dev -> dev`, with host overrides through `BEDC_PIPELINE_BRANCH`
and `BEDC_ROLLUP_TARGET_BRANCH`. The script never rebases target/source
branches and only force-updates the managed rollup branch with lease.
Use `--no-push` to construct and validate the candidate locally without
pushing or touching GitHub PR state.
"""

from __future__ import annotations

import argparse
import contextlib
import errno
import fcntl
import os
import re
import shutil
import subprocess
import sys
import time
import tempfile
from dataclasses import dataclass
from pathlib import Path

from bedc_quality_canonical_generated_merge import (
    CANONICAL_PREFIX,
    CanonicalGeneratedMergePolicy,
    PolicyError,
)
from host_context import host_path, host_value

REPO_ROOT = host_path(
    Path(__file__).resolve().parent.parent,
    "REPO_ROOT",
    default=Path(__file__).resolve().parent.parent,
)
def _source_branch_default() -> str:
    return host_value(REPO_ROOT, "BEDC_PIPELINE_BRANCH", default="codex-auto-dev")


def _mirror_branch_default() -> str:
    return host_value(REPO_ROOT, "BEDC_MIRROR_BRANCH", default="auto-dev")


def _upstream_branch_default() -> str:
    """Mirror tools/auto_heal_base.py BEDC_ROLLUP_TARGET_BRANCH topology.

    Keep this fallback chain synchronized with auto_heal_base when the rollup
    topology changes.
    """
    rollup_target = host_value(REPO_ROOT, "BEDC_ROLLUP_TARGET_BRANCH")
    if rollup_target is not None:
        return rollup_target
    return host_value(REPO_ROOT, "BEDC_UPSTREAM_BRANCH", default="dev")


SOURCE_BRANCH = host_value(REPO_ROOT, "BEDC_PIPELINE_BRANCH", default="codex-auto-dev")
MIRROR_BRANCH = host_value(REPO_ROOT, "BEDC_MIRROR_BRANCH", default="auto-dev")
UPSTREAM_BRANCH = _upstream_branch_default()
CODEX_PATH = host_value(REPO_ROOT, "BEDC_CODEX_PATH") or shutil.which("codex") or "codex"
VALIDATION_WORKTREE = host_path(
    REPO_ROOT,
    "BEDC_SYNC_VALIDATION_WORKTREE",
    default=Path(tempfile.gettempdir()) / ".bedc-sync-validate-wt",
)
VALIDATION_BRANCH = "bedc-sync-validate"
CONFLICT_PROMPT = """You are resolving git merge conflicts in the BEDC mathematics project.

The merge currently has unresolved conflicts. Files with `<<<<<<<` / `=======` / `>>>>>>>` markers:
{conflicted}

## Repository conventions

- `lean4/BEDC/**.lean`: when both sides added theorems / definitions / imports, keep the union. For genuinely incompatible signatures, keep the more substantive version (longer body, more named hypotheses, more BHist anchors).
- `papers/bedc/parts/**.tex`: both sides may have added `\\input{...}` lines, `\\leanchecked{...}` markers, theorems, definitions. Keep the union when content is additive. For LaTeX `\\label{...}` collisions, keep ONE copy (drop the duplicate label entirely; do not rename).
- `papers/bedc/parts/concrete_instances/`: this directory uses a hub+subdir layout. Whenever a `concrete_instances/<slug>/` subdirectory exists, the top-level numbered hub `NN_<slug>_namecert_construction.tex` MUST also exist (a thin orienting/router chapter that `\\input`s the subdir spine). `bedc_ci.py audit`'s orphan-subdir gate turns the subdir into a BLOCKING failure if the numbered hub is missing — this gate is the single most common cause of a failing rollup candidate. Therefore: NEVER resolve a conflict on `NN_<slug>_namecert_construction.tex` to deletion while its `<slug>/` subdir is present. On a modify/delete conflict (one side has the numbered hub, the other deleted it), KEEP the hub — take whichever side still has it (normally the incoming `origin/codex-auto-dev` / `:3:` version). When incoming migrated a flat chapter into hub+subdir layout, take incoming's full layout: keep BOTH the numbered top-level hub AND the `<slug>/` subdir spine; do not collapse them into the subdir alone. A numbered hub is never an "unreachable duplicate route" — it is the region marker the audit requires.
- `lean4/scripts/**` / `papers/bedc/scripts/**` / `*.py` / `*.sh`: prefer the side with newer behaviour (more recent commit, longer body, additional code paths). Read both sides' diffs before deciding.
- `MEMORY.md` / `CLAUDE.md` / `AGENTS.md` / `SKILL.md`: keep the union of bullet points / sections; if the same key was edited differently on both sides, keep the more specific / more recent version.

## Process

For each conflicted file:
1. `git diff :2:<path>` and `git diff :3:<path>` to see HEAD's vs incoming version.
2. Resolve manually (edit the file to drop conflict markers + chosen content).
3. After all files resolved: run `bash papers/bedc/scripts/check_tex_size.sh` if any conflicted file is under `papers/bedc/` and run `cd lean4 && lake build` only if a conflicted file is under `lean4/`.
4. Do NOT run `git add` or `git commit`; leave the resolved file contents in the working tree. The daemon will stage and commit under its shared lock.
5. Do NOT `git push`.

If you cannot resolve a conflict (genuinely incompatible semantic intent, build fails after resolution, etc.), run `git merge --abort` and explain in your final message what blocked the resolution.
"""


def run(cmd, *, cwd=REPO_ROOT, check=True, capture=False, env=None, timeout=None):
    """Run a subprocess; raise on non-zero unless check=False."""
    res = subprocess.run(
        cmd, cwd=cwd, env=env,
        capture_output=capture, text=True, timeout=timeout,
    )
    if check and res.returncode != 0:
        out = (res.stdout or "") + (res.stderr or "")
        raise RuntimeError(f"command failed (rc={res.returncode}): {' '.join(cmd)}\n{out}")
    return res


def git(*args, **kwargs):
    return run(["git", *args], **kwargs)


def acquire_main_checkout_lock(timeout: int = 120):
    """Acquire the shared branch lock from any linked worktree shape."""
    return _acquire_git_common_lock(SOURCE_BRANCH, timeout=timeout)


@contextlib.contextmanager
def _acquire_git_common_lock(branch: str, *, timeout: float | None = None):
    res = run(["git", "rev-parse", "--git-common-dir"],
              cwd=REPO_ROOT, capture=True, check=False)
    if res.returncode == 0 and res.stdout.strip():
        git_common = Path(res.stdout.strip())
        if not git_common.is_absolute():
            git_common = (REPO_ROOT / git_common).resolve()
    else:
        git_common = (REPO_ROOT / ".git").resolve()
    safe_branch = branch.replace("/", "__")
    path = git_common / f"{safe_branch}.push.lock"
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(str(path), os.O_RDWR | os.O_CREAT, 0o644)
    try:
        deadline = None if timeout is None else time.monotonic() + timeout
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError as exc:
                if exc.errno not in (errno.EWOULDBLOCK, errno.EAGAIN):
                    raise
                if timeout == 0:
                    raise BlockingIOError(
                        f"push lock for branch {branch!r} held by another process; "
                        f"lockfile {path}"
                    ) from exc
                if deadline is not None and time.monotonic() >= deadline:
                    raise TimeoutError(
                        f"push lock for branch {branch!r} held for more than "
                        f"{timeout}s by another process"
                    ) from exc
                time.sleep(0.5)
        try:
            os.ftruncate(fd, 0)
            os.write(fd, f"pid={os.getpid()} held_at={int(time.time())}\n".encode())
            yield path
        finally:
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            except OSError:
                pass
    finally:
        os.close(fd)


def current_branch() -> str:
    return git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()


def working_tree_dirty() -> bool:
    out = git("status", "--porcelain", capture=True).stdout
    return bool(out.strip())


def conflicted_files(cwd: Path = REPO_ROOT) -> list[str]:
    out = run(["git", "diff", "--name-only", "--diff-filter=U"],
              cwd=cwd, capture=True).stdout
    return [line for line in out.splitlines() if line]


def _canonical_paths(paths: list[str]) -> list[str]:
    return [path for path in paths if path.startswith(CANONICAL_PREFIX)]


def has_unmerged_index(cwd: Path = REPO_ROOT) -> bool:
    out = run(["git", "ls-files", "-u"], cwd=cwd,
              check=False, capture=True).stdout
    return bool(out.strip())


def has_conflict_markers(path: str, cwd: Path = REPO_ROOT) -> bool:
    try:
        text = (cwd / path).read_text(encoding="utf-8", errors="ignore")
    except FileNotFoundError:
        return False
    except Exception:
        return True
    return any(marker in text for marker in ("<<<<<<<", "=======", ">>>>>>>"))


def install_canonical_generated_merge_driver(cwd: Path = REPO_ROOT) -> bool:
    try:
        CanonicalGeneratedMergePolicy(cwd).install_driver()
        return True
    except PolicyError as exc:
        print(f"[sync] canonical generated merge driver install failed: {exc}",
              file=sys.stderr)
        return False


def collapse_canonical_generated_conflicts(cwd: Path = REPO_ROOT) -> bool:
    try:
        collapsed = CanonicalGeneratedMergePolicy(cwd).collapse_unmerged()
    except PolicyError as exc:
        print(f"[sync] canonical generated conflict collapse failed: {exc}",
              file=sys.stderr)
        return False
    if collapsed:
        print(f"[sync] collapsed {len(collapsed)} canonical generated conflict(s)")
    return True


def canonical_generated_driver_paths(cwd: Path = REPO_ROOT) -> list[str]:
    try:
        return CanonicalGeneratedMergePolicy(cwd).driver_marked_paths()
    except PolicyError as exc:
        print(f"[sync] canonical generated driver marker read failed: {exc}",
              file=sys.stderr)
        return []


def clear_canonical_generated_driver_paths(cwd: Path = REPO_ROOT) -> None:
    try:
        CanonicalGeneratedMergePolicy(cwd).clear_driver_marker()
    except PolicyError as exc:
        print(f"[sync] canonical generated driver marker clear failed: {exc}",
              file=sys.stderr)


def _has_merge_head(cwd: Path = REPO_ROOT) -> bool:
    return run(["git", "rev-parse", "--verify", "--quiet", "MERGE_HEAD"],
               cwd=cwd, check=False, capture=True).returncode == 0


def _canonical_generated_gate(cwd: Path = REPO_ROOT) -> bool:
    lab = cwd / "papers" / "bedc-quality-lab"
    if not lab.exists():
        print(f"[sync] canonical generated gate missing lab directory: {lab}",
              file=sys.stderr)
        return False

    verify_cmd = ["python3", "scripts/run_canonical_reports.py", "--verify-fingerprints"]
    regen_cmd = ["python3", "scripts/run_canonical_reports.py", "--cold"]

    regen = run(regen_cmd, cwd=lab, check=False, capture=True)
    if regen.returncode != 0:
        out = ((regen.stdout or "") + (regen.stderr or "")).strip().splitlines()
        msg = out[-1] if out else "no output"
        print(f"[sync] canonical generated producer regen failed rc={regen.returncode}: "
              f"{msg[:240]}", file=sys.stderr)
        return False

    verify = run(verify_cmd, cwd=lab, check=False, capture=True)
    if verify.returncode != 0:
        out = ((verify.stdout or "") + (verify.stderr or "")).strip().splitlines()
        msg = out[-1] if out else "no output"
        print(f"[sync] canonical generated fingerprint verify failed after regen "
              f"rc={verify.returncode}: {msg[:240]}", file=sys.stderr)
        return False

    run(["git", "add", "-A", "--", "papers/bedc-quality-lab/reports/canonical"],
        cwd=cwd, check=False, capture=True)
    print("[sync] canonical generated artifacts regenerated and verified")
    return True


def _commit_pending_merge(
    cwd: Path = REPO_ROOT,
    *,
    canonical_gate: bool,
    locked: bool = False,
) -> bool:
    if canonical_gate and not _canonical_generated_gate(cwd):
        return False
    if locked:
        run(["git", "commit", "--no-edit"], cwd=cwd)
        return True
    with acquire_main_checkout_lock(timeout=120):
        run(["git", "commit", "--no-edit"], cwd=cwd)
    return True


def finish_canonical_generated_only_merge(cwd: Path = REPO_ROOT) -> bool:
    if not _commit_pending_merge(cwd, canonical_gate=True):
        return False
    with acquire_main_checkout_lock(timeout=120):
        clear_canonical_generated_driver_paths(cwd)
    return True


def write_locked_git_wrapper(wrapper_dir: Path) -> dict[str, str]:
    real_git = shutil.which("git") or "/usr/bin/git"
    wrapper = wrapper_dir / "git"
    wrapper.write_text(
        "#!/usr/bin/env python3\n"
        "import errno\n"
        "import fcntl\n"
        "import os\n"
        "import subprocess\n"
        "import sys\n"
        "import time\n"
        "from contextlib import contextmanager\n"
        "from pathlib import Path\n"
        f"REAL_GIT = {real_git!r}\n"
        f"BRANCH = {SOURCE_BRANCH!r}\n"
        "WRITE_CMDS = {'add', 'commit', 'reset', 'checkout', 'merge', 'pull', 'stash', 'push'}\n"
        "argv = sys.argv[1:]\n"
        "cmd = argv[0] if argv else ''\n"
        "@contextmanager\n"
        "def acquire_push_lock(branch, timeout=120):\n"
        "    res = subprocess.run([REAL_GIT, 'rev-parse', '--git-common-dir'],\n"
        "                         capture_output=True, text=True)\n"
        "    git_common = Path(res.stdout.strip()) if res.returncode == 0 and res.stdout.strip() else Path('.git')\n"
        "    if not git_common.is_absolute():\n"
        "        git_common = (Path.cwd() / git_common).resolve()\n"
        "    path = git_common / f\"{branch.replace('/', '__')}.push.lock\"\n"
        "    path.parent.mkdir(parents=True, exist_ok=True)\n"
        "    fd = os.open(str(path), os.O_RDWR | os.O_CREAT, 0o644)\n"
        "    try:\n"
        "        deadline = time.monotonic() + timeout if timeout is not None else None\n"
        "        while True:\n"
        "            try:\n"
        "                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)\n"
        "                break\n"
        "            except OSError as exc:\n"
        "                if exc.errno not in (errno.EWOULDBLOCK, errno.EAGAIN):\n"
        "                    raise\n"
        "                if deadline is not None and time.monotonic() >= deadline:\n"
        "                    raise TimeoutError(f'push lock for branch {branch!r} timed out; lockfile {path}') from exc\n"
        "                time.sleep(0.5)\n"
        "        try:\n"
        "            os.ftruncate(fd, 0)\n"
        "            os.write(fd, f'pid={os.getpid()} held_at={int(time.time())}\\n'.encode())\n"
        "            yield path\n"
        "        finally:\n"
        "            fcntl.flock(fd, fcntl.LOCK_UN)\n"
        "    finally:\n"
        "        os.close(fd)\n"
        "def run_git():\n"
        "    return subprocess.call([REAL_GIT, *argv])\n"
        "try:\n"
        "    if cmd in WRITE_CMDS:\n"
        "        with acquire_push_lock(BRANCH, timeout=120):\n"
        "            sys.exit(run_git())\n"
        "    sys.exit(run_git())\n"
        "except TimeoutError as exc:\n"
        "    print(f'[sync] push lock timeout in codex git {cmd}: {exc}', file=sys.stderr)\n"
        "    sys.exit(75)\n",
        encoding="utf-8",
    )
    wrapper.chmod(0o755)
    env = os.environ.copy()
    env["PATH"] = str(wrapper_dir) + os.pathsep + env.get("PATH", "")
    return env


def call_codex_to_resolve(
    work_dir: Path,
    timeout: int = 1800,
    *,
    canonical_gate: bool = False,
) -> bool:
    """Invoke codex inside `work_dir` to resolve current merge conflicts.

    Returns True if codex completed and the merge has no remaining conflicts;
    False otherwise (caller should `git merge --abort`)."""
    files = conflicted_files(work_dir)
    if not files:
        return True

    # Use replacement rather than str.format because CONFLICT_PROMPT contains
    # literal LaTeX braces such as \label{...}, \input{...}, and \begin{...}.
    prompt = CONFLICT_PROMPT.replace(
        "{conflicted}", "\n".join(f"  {f}" for f in files),
    )
    prompt = render_prompt_host_context(prompt)

    if not Path(CODEX_PATH).exists():
        print(f"[sync] codex CLI not found at {CODEX_PATH}", file=sys.stderr)
        return False

    print(f"[sync] {len(files)} file(s) in conflict; invoking codex (cwd={work_dir})")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as pf:
        pf.write(prompt)
        prompt_file = pf.name

    cmd = [
        "timeout", str(timeout),
        CODEX_PATH, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C", str(work_dir),
        "-",
    ]
    try:
        with tempfile.TemporaryDirectory(prefix="bedc-sync-git-") as git_wrapper_dir:
            env = write_locked_git_wrapper(Path(git_wrapper_dir))
            with open(prompt_file, "r") as pf:
                res = subprocess.run(cmd, stdin=pf, cwd=work_dir, text=True, env=env)
    finally:
        os.unlink(prompt_file)

    if res.returncode != 0:
        print(f"[sync] codex exec returned rc={res.returncode}", file=sys.stderr)
        return False

    unresolved = [path for path in files if has_conflict_markers(path, work_dir)]
    if unresolved:
        print(f"[sync] codex left conflict markers: {unresolved}", file=sys.stderr)
        return False
    with acquire_main_checkout_lock(timeout=120):
        merge_head = run(["git", "rev-parse", "--verify", "--quiet", "MERGE_HEAD"],
                         cwd=work_dir, check=False, capture=True).returncode == 0
        if merge_head:
            run(["git", "add", "-A"], cwd=work_dir)
            remaining = conflicted_files(work_dir)
            if remaining:
                print(f"[sync] codex left unresolved index conflicts: {remaining}", file=sys.stderr)
                return False
            if not _commit_pending_merge(
                work_dir,
                canonical_gate=canonical_gate or bool(canonical_generated_driver_paths(work_dir)),
                locked=True,
            ):
                return False
            clear_canonical_generated_driver_paths(work_dir)
    return True


def render_prompt_host_context(prompt: str) -> str:
    replacements = {
        "codex-auto-dev": SOURCE_BRANCH,
        "auto-dev": MIRROR_BRANCH,
        "dev": UPSTREAM_BRANCH,
    }
    out = prompt
    for old, new in replacements.items():
        out = re.sub(
            rf"(?<![A-Za-z0-9_-]){re.escape(old)}(?![A-Za-z0-9_-])",
            new,
            out,
        )
    return out


def merge_with_codex_fallback(target: str, label: str,
                              *, cwd: Path = REPO_ROOT) -> bool:
    """Merge `target` into HEAD. On conflict, invoke codex once. Returns True on success."""
    print(f"[sync] {label}: merging {target}...")
    if not install_canonical_generated_merge_driver(cwd):
        return False
    clear_canonical_generated_driver_paths(cwd)
    with acquire_main_checkout_lock(timeout=120):
        res = run(["git", "merge", "--no-ff", "--no-commit", target],
                  cwd=cwd, check=False, capture=True)
    if res.returncode == 0:
        canonical_gate = bool(canonical_generated_driver_paths(cwd))
        if _has_merge_head(cwd):
            if not _commit_pending_merge(cwd, canonical_gate=canonical_gate):
                with acquire_main_checkout_lock(timeout=120):
                    run(["git", "merge", "--abort"], cwd=cwd, check=False)
                return False
            clear_canonical_generated_driver_paths(cwd)
        if canonical_gate:
            print(f"[sync] {label}: canonical generated merge verified")
        else:
            print(f"[sync] {label}: merge clean")
        return True

    # Non-zero: either no-op (already up to date) or conflict.
    out = (res.stdout or "") + (res.stderr or "")
    if "Already up to date" in out or "already up to date" in out:
        print(f"[sync] {label}: already up to date")
        clear_canonical_generated_driver_paths(cwd)
        return True

    initial_conflicts = conflicted_files(cwd)
    if not initial_conflicts:
        # Some other failure (e.g. dirty WT). Surface it.
        print(f"[sync] {label}: merge failed without conflicts:\n{out}", file=sys.stderr)
        return False
    canonical_conflicts = _canonical_paths(initial_conflicts)

    if not collapse_canonical_generated_conflicts(cwd):
        with acquire_main_checkout_lock(timeout=120):
            run(["git", "merge", "--abort"], cwd=cwd, check=False)
        return False

    remaining_conflicts = conflicted_files(cwd)
    canonical_gate = bool(canonical_generated_driver_paths(cwd)) or bool(canonical_conflicts)
    if not remaining_conflicts:
        if canonical_gate:
            committed = finish_canonical_generated_only_merge(cwd)
        else:
            committed = _commit_pending_merge(cwd, canonical_gate=False)
        if not committed:
            with acquire_main_checkout_lock(timeout=120):
                run(["git", "merge", "--abort"], cwd=cwd, check=False)
            return False
        print(f"[sync] {label}: canonical generated conflicts collapsed")
        return True

    if not call_codex_to_resolve(cwd, canonical_gate=canonical_gate):
        print(f"[sync] {label}: codex could not resolve; aborting merge", file=sys.stderr)
        with acquire_main_checkout_lock(timeout=120):
            run(["git", "merge", "--abort"], cwd=cwd, check=False)
        return False

    print(f"[sync] {label}: codex resolved conflicts and committed")
    return True


def merge_prefer_ff_with_codex_fallback(target: str, label: str,
                                        *, cwd: Path = REPO_ROOT) -> bool:
    print(f"[sync] {label}: fast-forward check {target}...")
    if not install_canonical_generated_merge_driver(cwd):
        return False
    with acquire_main_checkout_lock(timeout=120):
        ff = run(["git", "merge", "--ff-only", target],
                 cwd=cwd, check=False, capture=True)
    if ff.returncode == 0:
        print(f"[sync] {label}: fast-forwarded")
        return True
    return merge_with_codex_fallback(target, label=label, cwd=cwd)


def push_branch(branch: str, *, set_upstream: bool = False,
                max_attempts: int = 5) -> int:
    """Push `branch` to origin with retry-on-race. Returns final rc.

    Multi-producer branches (auto-dev gets pushed by bedc-deep
    supervisor + codex-auto-dev mirror + external PRs) race on the
    ref lock. A single push attempt loses that race ~constantly; the
    outer 600s daemon loop's retry cadence is too slow to win the
    window. Retry the push 5x with exponential backoff
    (1s, 2s, 4s, 8s, 16s — total ~31s in worst case) so a single
    daemon tick has multiple shots at the ref between external pushes.

    Each retry refetches origin and remerges so we push the latest
    incorporated tip, not a stale local tip that would just race again.

    Concurrency: wraps each push attempt in the orchestrator-shared
    codex-auto-dev lock so main-checkout index writers serialize with
    the other tools daemons and orchestrator merge paths.
    """
    env = os.environ.copy()
    env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
    backoff = 1.0
    last_rc = 1
    for attempt in range(1, max_attempts + 1):
        cmd = ["git", "push"]
        if set_upstream and attempt == 1:
            cmd.extend(["--set-upstream", "origin", branch])
        else:
            cmd.extend(["origin", branch])
        with acquire_main_checkout_lock(timeout=120):
            res = subprocess.run(cmd, cwd=REPO_ROOT, env=env)
        if res.returncode == 0:
            if attempt > 1:
                print(f"[sync] push {branch} succeeded on attempt {attempt}",
                      file=sys.stderr)
            return 0
        last_rc = res.returncode
        if attempt == max_attempts:
            break
        # Race condition: refetch + remerge before next push attempt.
        print(f"[sync] push {branch} attempt {attempt} failed; "
              f"refetch+remerge then retry in {backoff:.1f}s",
              file=sys.stderr)
        time.sleep(backoff)
        backoff = min(backoff * 2, 16.0)
        # Pull latest origin into branch via merge --no-ff so a fresh
        # SHA gets pushed. If the merge itself fails the retry stops.
        with acquire_main_checkout_lock(timeout=120):
            fetch = git("fetch", "origin", branch,
                        check=False, capture=True)
        if fetch.returncode != 0:
            print(f"[sync] push retry refetch failed: {fetch.stderr.strip()[:200]}",
                  file=sys.stderr)
            continue
        if not merge_with_codex_fallback(f"origin/{branch}",
                                         label=f"{branch} <- origin/{branch}"):
            print("[sync] push retry remerge could not incorporate remote tip",
                  file=sys.stderr)
            return last_rc
    return last_rc


def push_head_to_branch_from_worktree(cwd: Path, branch: str,
                                      *, max_attempts: int = 5) -> int:
    env = os.environ.copy()
    env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
    backoff = 1.0
    last_rc = 1
    for attempt in range(1, max_attempts + 1):
        with acquire_main_checkout_lock(timeout=120):
            res = run(["git", "push", "origin", f"HEAD:refs/heads/{branch}"],
                      cwd=cwd, env=env, check=False, capture=True)
        if res.returncode == 0:
            if attempt > 1:
                print(f"[sync] isolated push {branch} succeeded on attempt {attempt}",
                      file=sys.stderr)
            return 0
        last_rc = res.returncode
        if attempt == max_attempts:
            break
        print(f"[sync] isolated push {branch} attempt {attempt} failed; "
              f"fetching origin/{branch} before another attempt",
              file=sys.stderr)
        time.sleep(backoff)
        backoff = min(backoff * 2, 16.0)
        with acquire_main_checkout_lock(timeout=120):
            fetch = run(["git", "fetch", "origin", branch],
                        cwd=cwd, check=False, capture=True)
        if fetch.returncode != 0:
            print(f"[sync] isolated push fetch failed: "
                  f"{((fetch.stdout or '') + (fetch.stderr or '')).strip()[:200]}",
                  file=sys.stderr)
            continue
        if not merge_prefer_ff_with_codex_fallback(
            f"origin/{branch}", label=f"{branch} <- origin/{branch}", cwd=cwd,
        ):
            print("[sync] isolated push could not incorporate remote tip",
                  file=sys.stderr)
            return last_rc
    return last_rc


def sync_mirror_convergence_in_worktree(*, no_push: bool) -> bool:
    """Converge the two managed branches without touching the main checkout index."""
    print("[sync] unmerged index entries in main checkout; using isolated worktree")
    print("[sync] dev -> auto-dev validation skipped; it requires the clean checkout path")
    with acquire_main_checkout_lock(timeout=120):
        fetch = git("fetch", "origin", "--prune", check=False, capture=True)
    if fetch.returncode != 0:
        print(f"[sync] isolated fetch failed: "
              f"{((fetch.stdout or '') + (fetch.stderr or '')).strip()[:240]}",
              file=sys.stderr)
        return False
    for branch in (MIRROR_BRANCH, SOURCE_BRANCH):
        if not has_remote_branch(branch):
            print(f"[sync] origin/{branch} missing; cannot run isolated convergence",
                  file=sys.stderr)
            return False

    temp_root = Path(tempfile.mkdtemp(prefix="bedc-sync-"))
    worktree = temp_root / "worktree"
    temp_branch = f"bedc-sync-isolated-{os.getpid()}-{int(time.time())}"
    try:
        with acquire_main_checkout_lock(timeout=120):
            add = git("worktree", "add", "-b", temp_branch, str(worktree),
                      f"origin/{MIRROR_BRANCH}", check=False, capture=True)
        if add.returncode != 0:
            print(f"[sync] isolated worktree add failed: "
                  f"{((add.stdout or '') + (add.stderr or '')).strip()[:240]}",
                  file=sys.stderr)
            return False

        if not merge_prefer_ff_with_codex_fallback(
            f"origin/{SOURCE_BRANCH}",
            label=f"{MIRROR_BRANCH} <- origin/{SOURCE_BRANCH}",
            cwd=worktree,
        ):
            return False
        mirror_ref = run(["git", "rev-parse", "HEAD"], cwd=worktree,
                         capture=True).stdout.strip()
        if not no_push:
            rc = push_head_to_branch_from_worktree(worktree, MIRROR_BRANCH)
            if rc != 0:
                print(f"[sync] isolated push origin {MIRROR_BRANCH} failed (rc={rc})",
                      file=sys.stderr)
                return False
            with acquire_main_checkout_lock(timeout=120):
                fetch = run(["git", "fetch", "origin", "--prune"],
                            cwd=worktree, check=False, capture=True)
            if fetch.returncode != 0:
                print("[sync] isolated fetch after mirror push failed",
                      file=sys.stderr)
                return False
            mirror_ref = f"origin/{MIRROR_BRANCH}"

        with acquire_main_checkout_lock(timeout=120):
            checkout = run(["git", "checkout", "-B", temp_branch,
                            f"origin/{SOURCE_BRANCH}"],
                           cwd=worktree, check=False, capture=True)
        if checkout.returncode != 0:
            print(f"[sync] isolated checkout of origin/{SOURCE_BRANCH} failed: "
                  f"{((checkout.stdout or '') + (checkout.stderr or '')).strip()[:240]}",
                  file=sys.stderr)
            return False
        if not merge_prefer_ff_with_codex_fallback(
            mirror_ref,
            label=f"{SOURCE_BRANCH} <- {mirror_ref}",
            cwd=worktree,
        ):
            return False
        if not no_push:
            rc = push_head_to_branch_from_worktree(worktree, SOURCE_BRANCH)
            if rc != 0:
                print(f"[sync] isolated push origin {SOURCE_BRANCH} failed (rc={rc})",
                      file=sys.stderr)
                return False
        return True
    except TimeoutError as exc:
        print(f"[sync] push lock timeout during isolated convergence: {exc}",
              file=sys.stderr)
        return False
    finally:
        if worktree.exists():
            run(["git", "merge", "--abort"], cwd=worktree,
                check=False, capture=True)
        with acquire_main_checkout_lock(timeout=120):
            git("worktree", "remove", "--force", str(worktree),
                check=False, capture=True)
            git("worktree", "prune", check=False, capture=True)
            git("branch", "-D", temp_branch, check=False, capture=True)
        shutil.rmtree(temp_root, ignore_errors=True)


def has_remote_branch(branch: str) -> bool:
    res = git("ls-remote", "--exit-code", "--heads", "origin", branch,
              check=False, capture=True)
    return res.returncode == 0


def has_upstream(branch: str) -> bool:
    res = git("rev-parse", "--abbrev-ref", f"{branch}@{{upstream}}",
              check=False, capture=True)
    return res.returncode == 0


def has_local_branch(branch: str) -> bool:
    res = git("rev-parse", "--verify", "--quiet", f"refs/heads/{branch}",
              check=False, capture=True)
    return res.returncode == 0


def ensure_local_tracks_origin(branch: str) -> bool:
    """If `branch` exists locally, fast-forward it to origin/<branch>.
    Else create it from origin/<branch>. Returns True on success."""
    if not has_remote_branch(branch):
        print(f"[sync] origin/{branch} missing — cannot sync", file=sys.stderr)
        return False
    if has_local_branch(branch):
        # Switch and converge with origin. Try ff first to keep history
        # clean; if local branch has diverged from origin/<branch>
        # (typically because an external worker — e.g. bedc-deep
        # supervisor — pushed commits to origin while local has its own
        # bookkeeping merges), fall back to a real merge with codex
        # conflict resolution. Leaving the divergence as-is wedges the
        # rest of the sync (push step gets `non-fast-forward` rejection
        # forever).
        with acquire_main_checkout_lock(timeout=120):
            git("checkout", branch)
            ff = git("merge", "--ff-only", f"origin/{branch}",
                     check=False, capture=True)
        if ff.returncode == 0:
            return True
        print(f"[sync] {branch} cannot ff origin/{branch} (diverged); "
              f"falling back to merge --no-ff with codex resolver",
              file=sys.stderr)
        if not merge_with_codex_fallback(f"origin/{branch}",
                                         label=f"{branch} <- origin/{branch}"):
            print(f"[sync] {branch} <- origin/{branch}: convergence failed",
                  file=sys.stderr)
            return False
        return True
    # Create new local tracking branch from origin.
    with acquire_main_checkout_lock(timeout=120):
        git("checkout", "-b", branch, f"origin/{branch}")
    return True


def sync_one_direction(target: str, source: str, *, no_push: bool) -> bool:
    """Checkout `target`, merge `source` into it, push origin/<target>.
    Returns True on success."""
    try:
        if not ensure_local_tracks_origin(target):
            return False
        label = f"{target} <- {source}"
        if not merge_with_codex_fallback(source, label=label):
            return False
        if no_push:
            return True
        rc = push_branch(target)
    except TimeoutError as exc:
        print(f"[sync] push lock timeout while syncing {target}: {exc}",
              file=sys.stderr)
        return False
    if rc != 0:
        print(f"[sync] push origin {target} failed (rc={rc})", file=sys.stderr)
        return False
    return True


def _rev_list_count(range_expr: str) -> int:
    res = run(["git", "rev-list", "--count", range_expr],
              capture=True, check=False)
    if res.returncode != 0:
        return 0
    out = res.stdout.strip()
    return int(out) if out.isdigit() else 0


def _origin_sha(branch: str) -> str | None:
    res = run(["git", "rev-parse", f"origin/{branch}"],
              capture=True, check=False)
    if res.returncode != 0:
        return None
    return res.stdout.strip() or None


def _remove_validation_worktree() -> None:
    """Tear down the scratch validation worktree so the next cycle recreates it
    cleanly.

    `git worktree remove --force` itself fails with "Directory not empty" when a
    previous validation crashed mid-run and left untracked files (or an
    inconsistent `.git/worktrees` entry). When that happens the subsequent
    `git worktree add` collides with the leftover directory and fails, so
    dev->auto-dev validation never even reaches the merge/regen/build steps and
    the sync wedges every cycle FOREVER (the failure is deterministic, not
    transient). Belt-and-suspenders: after the soft remove, unconditionally
    `rm -rf` any remnant, prune the stale worktree metadata, and drop the
    scratch branch — each step is harmless when already clean."""
    if VALIDATION_WORKTREE.exists():
        res = git("worktree", "remove", "--force", str(VALIDATION_WORKTREE),
                  check=False, capture=True)
        if res.returncode != 0:
            print(f"[sync] dev->auto-dev validation: soft worktree remove failed "
                  f"({((res.stdout or '') + (res.stderr or '')).strip()[:160]}); "
                  f"forcing rm -rf + prune")
    if VALIDATION_WORKTREE.exists():
        run(["rm", "-rf", str(VALIDATION_WORKTREE)], check=False, capture=True)
    git("worktree", "prune", check=False, capture=True)
    git("branch", "-D", VALIDATION_BRANCH, check=False, capture=True)


def _run_validation_gate(cmd: list[str], *, cwd: Path, label: str,
                         timeout: int | None = None) -> bool:
    try:
        res = run(cmd, cwd=cwd, check=False, capture=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print(f"[sync] dev->auto-dev validation: {label} timed out after {timeout}s")
        return False
    except Exception as exc:
        print(f"[sync] dev->auto-dev validation: {label} could not run: {exc}")
        return False
    if res.returncode == 0:
        return True
    out = ((res.stdout or "") + (res.stderr or "")).strip().splitlines()
    tail = out[-1] if out else "no output"
    print(f"[sync] dev->auto-dev validation: {label} failed rc={res.returncode}: {tail[:240]}")
    return False


def _regen_manifest(cwd: Path) -> None:
    """Regenerate lean4/BEDC.lean from on-disk files after a merge, folding any
    change into the just-created merge commit.

    A conflict-free (clean) merge of BEDC.lean does NOT invoke the
    `bedc-lean-regen` merge driver (git only runs a custom merge driver on a
    file that actually conflicts). So when one side deleted a `.lean` file and
    the other side's manifest still carried its `import` line, the textually
    merged BEDC.lean keeps importing the now-missing module -> `lake build`
    fails with "no such file or directory" -> dev->auto-dev validation fails
    and the daemon skips forever ("waits for next passing tick"), since this
    failure mode reproduces deterministically and is neither a textual conflict
    (so codex-fallback never fires) nor transient. Regenerating from the actual
    filesystem drops imports of deleted modules and adds new ones, making the
    merged manifest consistent before the build gate runs."""
    regen = run(["python3", "lean4/scripts/regenerate_bedc_lean.py"],
                cwd=cwd, check=False, capture=True)
    if regen.returncode != 0:
        print(f"[sync] regenerate_bedc_lean failed rc={regen.returncode}: "
              f"{((regen.stdout or '') + (regen.stderr or '')).strip()[:200]}",
              file=sys.stderr)
        return
    status = run(["git", "status", "--porcelain", "lean4/BEDC.lean"],
                 cwd=cwd, check=False, capture=True)
    if (status.stdout or "").strip():
        run(["git", "add", "lean4/BEDC.lean"], cwd=cwd, check=False, capture=True)
        run(["git", "commit", "--amend", "--no-edit"], cwd=cwd,
            check=False, capture=True)
        print("[sync] regenerated BEDC.lean manifest after merge "
              "(folded into merge commit)")


def _restore_orphan_concrete_hubs(cwd: Path, source_branch: str) -> None:
    """Restore numbered concrete_instances hub files the merge silently dropped.

    `bedc_ci.py audit`'s orphan-subdir gate requires every
    `concrete_instances/<slug>/` subdir to be named by a top-level
    `NN_<slug>_namecert_construction.tex` hub (or a `Derived/<X>Up.lean`). When
    the target branch deleted such a hub (e.g. a "clean-name layout" cleanup
    that dropped NN_ files) while the source still carries it AND the source did
    not re-touch it since the merge-base, a 3-way merge silently applies the
    target's deletion with NO conflict — so the codex conflict resolver never
    sees it and the candidate ships an orphaned subdir that fails precheck every
    cycle. Re-checkout each orphaned subdir's numbered hub from
    `origin/<source_branch>` (the rollup's intent is to bring the source layout
    forward) and fold the restore into the merge commit. This complements the
    CONFLICT_PROMPT hub rule, which only covers the conflicting case."""
    instances = cwd / "papers" / "bedc" / "parts" / "concrete_instances"
    if not instances.exists():
        return
    derived = cwd / "lean4" / "BEDC" / "Derived"
    lean_regions: set[str] = set()
    if derived.exists():
        for p in derived.iterdir():
            stem = p.stem if p.is_file() else p.name
            if stem.endswith("Up"):
                core = stem[:-2]
                lean_regions.add(re.sub(r"([a-z])([A-Z])", r"\1_\2", core).lower())
    hub_re = re.compile(r"^\d+_([a-z][a-z0-9_]*)_namecert_construction\.tex$")
    paper_regions: set[str] = set()
    for f in instances.iterdir():
        if f.is_file():
            m = hub_re.match(f.name)
            if m:
                paper_regions.add(m.group(1))
    known = lean_regions | paper_regions
    orphan_slugs = sorted(
        sub.name for sub in instances.iterdir()
        if sub.is_dir() and sub.name not in known
    )
    if not orphan_slugs:
        return
    ls = run(["git", "ls-tree", "--name-only", f"origin/{source_branch}",
              "papers/bedc/parts/concrete_instances/"],
             cwd=cwd, check=False, capture=True)
    source_hubs: dict[str, str] = {}
    for line in (ls.stdout or "").splitlines():
        line = line.strip()
        m = hub_re.match(Path(line).name)
        if m:
            source_hubs[m.group(1)] = line
    restored: list[str] = []
    for slug in orphan_slugs:
        hub_path = source_hubs.get(slug)
        if not hub_path:
            continue
        co = run(["git", "checkout", f"origin/{source_branch}", "--", hub_path],
                 cwd=cwd, check=False, capture=True)
        if co.returncode == 0:
            restored.append(hub_path)
    if not restored:
        return
    run(["git", "add", *restored], cwd=cwd, check=False, capture=True)
    run(["git", "commit", "--amend", "--no-edit"], cwd=cwd,
        check=False, capture=True)
    print(f"[sync] rollup: restored {len(restored)} numbered concrete hub(s) "
          f"orphaned by silent merge deletion "
          f"(folded into merge commit): {', '.join(Path(p).name for p in restored)}")


def validate_dev_merge_in_worktree() -> tuple[bool, str | None, str | None]:
    """Validate origin/dev -> auto-dev in an isolated worktree before push."""
    if _rev_list_count(f"origin/{MIRROR_BRANCH}..origin/{UPSTREAM_BRANCH}") == 0:
        print("[sync] dev->auto-dev: no new dev commits; skipping validation")
        return True, _origin_sha(UPSTREAM_BRANCH), _origin_sha(MIRROR_BRANCH)

    dev_sha = _origin_sha(UPSTREAM_BRANCH)
    mirror_sha = _origin_sha(MIRROR_BRANCH)
    if not dev_sha or not mirror_sha:
        print("[sync] dev->auto-dev validation: missing origin SHA")
        return False, dev_sha, mirror_sha

    _remove_validation_worktree()
    git("branch", "-D", VALIDATION_BRANCH, check=False, capture=True)
    add = git("worktree", "add", "-b", VALIDATION_BRANCH, str(VALIDATION_WORKTREE),
              f"origin/{MIRROR_BRANCH}", check=False, capture=True)
    if add.returncode != 0:
        print(f"[sync] dev->auto-dev validation: worktree add failed: "
              f"{((add.stdout or '') + (add.stderr or '')).strip()[:240]}")
        return False, dev_sha, mirror_sha

    if not install_canonical_generated_merge_driver(VALIDATION_WORKTREE):
        return False, dev_sha, mirror_sha
    clear_canonical_generated_driver_paths(VALIDATION_WORKTREE)

    merge = run(["git", "merge", "--no-ff", "--no-commit", dev_sha],
                cwd=VALIDATION_WORKTREE, check=False, capture=True)
    if merge.returncode == 0:
        canonical_gate = bool(canonical_generated_driver_paths(VALIDATION_WORKTREE))
        if _has_merge_head(VALIDATION_WORKTREE):
            if not _commit_pending_merge(
                VALIDATION_WORKTREE,
                canonical_gate=canonical_gate,
            ):
                run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
                    check=False, capture=True)
                return False, dev_sha, mirror_sha
            clear_canonical_generated_driver_paths(VALIDATION_WORKTREE)
    if merge.returncode != 0:
        initial_conflicts = conflicted_files(VALIDATION_WORKTREE)
        if initial_conflicts:
            canonical_conflicts = _canonical_paths(initial_conflicts)
            if not collapse_canonical_generated_conflicts(VALIDATION_WORKTREE):
                run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
                    check=False, capture=True)
                print("[sync] dev->auto-dev validation: canonical collapse failed")
                return False, dev_sha, mirror_sha
            remaining_conflicts = conflicted_files(VALIDATION_WORKTREE)
            if not remaining_conflicts:
                canonical_gate = (
                    bool(canonical_generated_driver_paths(VALIDATION_WORKTREE))
                    or bool(canonical_conflicts)
                )
                if not _commit_pending_merge(
                    VALIDATION_WORKTREE,
                    canonical_gate=canonical_gate,
                ):
                    run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
                        check=False, capture=True)
                    return False, dev_sha, mirror_sha
                clear_canonical_generated_driver_paths(VALIDATION_WORKTREE)
                print("[sync] dev->auto-dev validation: canonical generated conflicts collapsed")
            else:
                run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
                    check=False, capture=True)
                print(f"[sync] dev->auto-dev validation: source conflicts remain "
                      f"after canonical collapse: {remaining_conflicts}")
                return False, dev_sha, mirror_sha
        else:
            run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
                check=False, capture=True)
            print(f"[sync] dev->auto-dev validation: merge failed rc={merge.returncode}")
            return False, dev_sha, mirror_sha

    if merge.returncode != 0 and conflicted_files(VALIDATION_WORKTREE):
        run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
            check=False, capture=True)
        print(f"[sync] dev->auto-dev validation: merge failed rc={merge.returncode}")
        return False, dev_sha, mirror_sha

    _regen_manifest(VALIDATION_WORKTREE)

    if not _run_validation_gate(["make", "warn"],
                                cwd=VALIDATION_WORKTREE / "papers" / "bedc",
                                label="make warn"):
        return False, dev_sha, mirror_sha
    if not _run_validation_gate(["python3", "lean4/scripts/bedc_ci.py", "audit"],
                                cwd=VALIDATION_WORKTREE,
                                label="bedc_ci audit"):
        return False, dev_sha, mirror_sha
    if not _run_validation_gate(["lake", "build"],
                                cwd=VALIDATION_WORKTREE / "lean4",
                                label="lake build", timeout=1800):
        return False, dev_sha, mirror_sha

    print("[sync] dev->auto-dev validation: merge and local gates passed")
    return True, dev_sha, mirror_sha


def sync_dev_to_auto_dev_validated(*, no_push: bool) -> bool:
    """Validate dev -> auto-dev in a scratch worktree, then apply in main checkout."""
    if _rev_list_count(f"origin/{MIRROR_BRANCH}..origin/{UPSTREAM_BRANCH}") == 0:
        print("[sync] dev->auto-dev: no new dev commits; skipping")
        return True
    ok, dev_sha, mirror_sha = validate_dev_merge_in_worktree()
    if not ok:
        return False
    if _origin_sha(UPSTREAM_BRANCH) != dev_sha or _origin_sha(MIRROR_BRANCH) != mirror_sha:
        print("[sync] dev->auto-dev: origin moved after validation; retry next cycle")
        return False
    if no_push:
        return sync_one_direction(MIRROR_BRANCH, dev_sha, no_push=True)

    try:
        with acquire_main_checkout_lock(timeout=120):
            if has_local_branch(MIRROR_BRANCH):
                git("checkout", MIRROR_BRANCH)
                ff = git("merge", "--ff-only", mirror_sha, check=False, capture=True)
                if ff.returncode != 0:
                    print("[sync] dev->auto-dev: local auto-dev cannot fast-forward to validated base")
                    return False
            else:
                git("checkout", "-b", MIRROR_BRANCH, mirror_sha)
            if not install_canonical_generated_merge_driver(REPO_ROOT):
                return False
            clear_canonical_generated_driver_paths(REPO_ROOT)
            merge = git("merge", "--no-ff", "--no-commit", dev_sha,
                        check=False, capture=True)
            if merge.returncode == 0:
                canonical_gate = bool(canonical_generated_driver_paths(REPO_ROOT))
                if _has_merge_head(REPO_ROOT):
                    if not _commit_pending_merge(
                        REPO_ROOT,
                        canonical_gate=canonical_gate,
                        locked=True,
                    ):
                        git("merge", "--abort", check=False, capture=True)
                        return False
                    clear_canonical_generated_driver_paths(REPO_ROOT)
            if merge.returncode != 0:
                initial_conflicts = conflicted_files(REPO_ROOT)
                if not initial_conflicts:
                    git("merge", "--abort", check=False, capture=True)
                    print("[sync] dev->auto-dev: validated merge failed in main checkout; retry next cycle")
                    return False
                canonical_conflicts = _canonical_paths(initial_conflicts)
                if collapse_canonical_generated_conflicts(REPO_ROOT):
                    if not conflicted_files(REPO_ROOT):
                        canonical_gate = (
                            bool(canonical_generated_driver_paths(REPO_ROOT))
                            or bool(canonical_conflicts)
                        )
                        if not _commit_pending_merge(
                            REPO_ROOT,
                            canonical_gate=canonical_gate,
                            locked=True,
                        ):
                            git("merge", "--abort", check=False, capture=True)
                            return False
                        clear_canonical_generated_driver_paths(REPO_ROOT)
                        print("[sync] dev->auto-dev: canonical generated conflicts collapsed")
                    else:
                        git("merge", "--abort", check=False, capture=True)
                        print("[sync] dev->auto-dev: source conflicts after "
                              "canonical collapse; retry next cycle")
                        return False
                else:
                    git("merge", "--abort", check=False, capture=True)
                    print("[sync] dev->auto-dev: canonical collapse failed; retry next cycle")
                    return False
            if merge.returncode != 0 and conflicted_files(REPO_ROOT):
                git("merge", "--abort", check=False, capture=True)
                print("[sync] dev->auto-dev: validated merge failed in main checkout; retry next cycle")
                return False
            _regen_manifest(REPO_ROOT)
            push = run(["git", "push", "origin", f"HEAD:refs/heads/{MIRROR_BRANCH}"],
                       check=False, capture=True)
            if push.returncode != 0:
                print(f"[sync] dev->auto-dev: push failed after validation rc={push.returncode}; "
                      f"retry next cycle")
                return False
            git("fetch", "origin", "--prune", check=False, capture=True)
    except TimeoutError as exc:
        print(f"[sync] push lock timeout during validated dev merge: {exc}",
              file=sys.stderr)
        return False
    print("[sync] dev->auto-dev: pushed locally validated merge")
    return True


def _restore_autostash(stash_oid: str | None) -> None:
    """Re-apply our own autostash by OID, never leaving the main checkout
    dirty across ticks.

    Replaces the old `git stash pop check=False`, which had two fatal flaws:
    (1) it popped `stash@{0}` — the top of the SHARED stack — so it could
    discard a sibling worker's stash; (2) on a pop conflict it silently kept
    the stash AND left the working tree with unmerged paths / leftover
    untracked files, so every subsequent tick saw a dirty tree, stashed
    again, and re-conflicted — the engine behind the 394-deep stash pile and
    the auto-dev starvation.

    New behaviour: apply the EXACT OID we stashed (not the top of stack); on
    a clean apply, drop our stash so it does not accumulate; on conflict,
    hard-reset tracked files to HEAD (the committed pipeline state — what we
    discard is preserved in the kept stash) so no unmerged paths cross the
    tick boundary, and keep the stash on the stack for manual / GC recovery.
    We deliberately do NOT `git clean -fd` here: untracked files created by
    other daemons during our tick are not ours to delete.
    """
    if not stash_oid:
        # OID capture failed right after a successful `stash push` (rare). The
        # local changes ARE safely stashed (push -u already cleaned the tree),
        # we just don't know which entry is ours. NEVER fall back to
        # `stash@{0}` — the stack is shared across all worktrees, so the top
        # may be another process's stash. Leave our stash on the stack for
        # manual / GC recovery instead of risking a wrong-stash apply/drop.
        print("[sync] autostash OID was not captured; NOT touching stash@{0} "
              "(shared stack); leaving our stash on the stack for GC/manual "
              "recovery", file=sys.stderr)
        return
    ref = stash_oid
    short = ref[:12]
    print(f"[sync] restoring autostash {short}")
    try:
        with acquire_main_checkout_lock(timeout=120):
            apply = git("stash", "apply", ref, check=False, capture=True)
            if apply.returncode == 0:
                # Clean re-apply: drop our stash so the stack does not grow.
                git("stash", "drop", ref, check=False, capture=True)
                return
            out = ((apply.stdout or "") + (apply.stderr or "")).strip()[:240]
            print(f"[sync] autostash re-apply failed ({out}); hard-resetting tracked "
                  f"files to HEAD and quarantining stash {short} for GC/manual "
                  f"recovery (NOT cleaning untracked — may belong to other daemons)",
                  file=sys.stderr)
            git("reset", "--hard", "HEAD", check=False, capture=True)
    except TimeoutError as exc:
        print(f"[sync] push lock timeout while restoring autostash {short}: {exc}",
              file=sys.stderr)


@dataclass
class RollupCandidate:
    worktree: Path
    temp_root: Path
    temp_branch: str
    sha: str


def _branch_slug(branch: str) -> str:
    slug = branch.strip().removeprefix("origin/")
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", slug)
    slug = re.sub(r"-+", "-", slug).strip("-._")
    return slug.lower() or "branch"


def _rollup_branch_name(source: str, target: str) -> str:
    return f"rollup-{_branch_slug(source)}-to-{_branch_slug(target)}"


def _merge_base_contains(ancestor: str, descendant: str, *, cwd: Path = REPO_ROOT) -> bool:
    res = run(["git", "merge-base", "--is-ancestor", ancestor, descendant],
              cwd=cwd, check=False, capture=True)
    return res.returncode == 0


def _no_commits_between_error(output: str) -> bool:
    return "no commits between" in output.lower()


def _remote_branch_points_at(branch: str, sha: str) -> bool:
    branch_sha = _origin_sha(branch)
    return branch_sha is not None and branch_sha == sha


def _has_open_pr_for_head(branch: str, target_branch: str) -> bool | None:
    try:
        res = run(["gh", "pr", "list",
                   "--base", target_branch,
                   "--head", branch,
                   "--state", "open",
                   "--json", "number",
                   "--limit", "1"],
                  capture=True, check=False)
        if res.returncode != 0:
            print(f"[sync] rollup: warning: gh pr list by head failed: "
                  f"{((res.stdout or '') + (res.stderr or '')).strip()[:300]}",
                  file=sys.stderr)
            return None
        import json as _json
        rows = _json.loads(res.stdout or "[]")
    except Exception as exc:
        print(f"[sync] rollup: warning: could not inspect PRs by head: {exc}",
              file=sys.stderr)
        return None
    return bool(rows)


def _delete_managed_rollup_branch_if_no_pr(rollup_branch: str,
                                           target_branch: str) -> None:
    if not _gh_available():
        print(f"[sync] rollup: warning: gh CLI missing; cannot confirm "
              f"whether {rollup_branch} has an open PR before no-op cleanup",
              file=sys.stderr)
        return
    target_sha = _origin_sha(target_branch)
    if target_sha is None:
        return
    if not has_remote_branch(rollup_branch):
        return
    if not _remote_branch_points_at(rollup_branch, target_sha):
        return
    open_pr = _has_open_pr_for_head(rollup_branch, target_branch)
    if open_pr is None or open_pr:
        return
    with acquire_main_checkout_lock(timeout=120):
        delete = git("push", "origin", "--delete", rollup_branch,
                     check=False, capture=True)
    if delete.returncode == 0:
        print(f"[sync] rollup: deleted no-op managed branch {rollup_branch}")
    else:
        out = ((delete.stdout or "") + (delete.stderr or "")).strip()[:300]
        print(f"[sync] rollup: warning: could not delete no-op branch "
              f"{rollup_branch}: {out}", file=sys.stderr)


def _remove_rollup_worktree(candidate: RollupCandidate | None) -> None:
    if not candidate:
        return
    if candidate.worktree.exists():
        run(["git", "merge", "--abort"], cwd=candidate.worktree,
            check=False, capture=True)
    with acquire_main_checkout_lock(timeout=120):
        git("worktree", "remove", "--force", str(candidate.worktree),
            check=False, capture=True)
        git("worktree", "prune", check=False, capture=True)
        git("branch", "-D", candidate.temp_branch, check=False, capture=True)
    shutil.rmtree(candidate.temp_root, ignore_errors=True)


def _build_rollup_candidate(source_branch: str, target_branch: str) -> RollupCandidate | None:
    temp_root = Path(tempfile.mkdtemp(prefix="bedc-rollup-"))
    worktree = temp_root / "worktree"
    temp_branch = f"rollup-scratch-{_branch_slug(source_branch)}-to-{_branch_slug(target_branch)}-{os.getpid()}"
    try:
        with acquire_main_checkout_lock(timeout=120):
            add = git("worktree", "add", "-b", temp_branch, str(worktree),
                      f"origin/{target_branch}", check=False, capture=True)
        if add.returncode != 0:
            print(f"[sync] rollup: worktree add failed: "
                  f"{((add.stdout or '') + (add.stderr or '')).strip()[:400]}",
                  file=sys.stderr)
            shutil.rmtree(temp_root, ignore_errors=True)
            return None

        print(f"[sync] rollup: merging origin/{source_branch} into origin/{target_branch}")
        if not install_canonical_generated_merge_driver(worktree):
            _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
            return None
        clear_canonical_generated_driver_paths(worktree)
        merge = run(["git", "merge", "--no-ff", "--no-commit", f"origin/{source_branch}"],
                    cwd=worktree, check=False, capture=True)
        if merge.returncode == 0:
            canonical_gate = bool(canonical_generated_driver_paths(worktree))
            if _has_merge_head(worktree):
                if not _commit_pending_merge(worktree, canonical_gate=canonical_gate):
                    run(["git", "merge", "--abort"], cwd=worktree,
                        check=False, capture=True)
                    _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
                    return None
                clear_canonical_generated_driver_paths(worktree)
        if merge.returncode != 0:
            out = (merge.stdout or "") + (merge.stderr or "")
            initial_conflicts = conflicted_files(worktree)
            if initial_conflicts:
                canonical_conflicts = _canonical_paths(initial_conflicts)
                print("[sync] rollup: merge conflicted; collapsing canonical generated paths")
                if not collapse_canonical_generated_conflicts(worktree):
                    print("[sync] rollup: canonical collapse failed",
                          file=sys.stderr)
                    run(["git", "merge", "--abort"], cwd=worktree,
                        check=False, capture=True)
                    _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
                    return None
                remaining_conflicts = conflicted_files(worktree)
                canonical_gate = (
                    bool(canonical_generated_driver_paths(worktree))
                    or bool(canonical_conflicts)
                )
                if remaining_conflicts:
                    print("[sync] rollup: source conflicts remain; invoking codex resolver")
                    if not call_codex_to_resolve(worktree, canonical_gate=canonical_gate):
                        print("[sync] rollup: codex could not resolve merge",
                              file=sys.stderr)
                        run(["git", "merge", "--abort"], cwd=worktree,
                            check=False, capture=True)
                        _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
                        return None
                else:
                    if not _commit_pending_merge(worktree, canonical_gate=canonical_gate):
                        run(["git", "merge", "--abort"], cwd=worktree,
                            check=False, capture=True)
                        _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
                        return None
                    clear_canonical_generated_driver_paths(worktree)
                    print("[sync] rollup: canonical generated conflicts collapsed")
            elif "Already up to date" in out or "already up to date" in out:
                print("[sync] rollup: source already included in target")
            else:
                print(f"[sync] rollup: merge failed without conflicts: "
                      f"{out.strip()[:400]}", file=sys.stderr)
                _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
                return None

        _regen_manifest(worktree)
        _restore_orphan_concrete_hubs(worktree, source_branch)
        dirty = run(["git", "status", "--porcelain"], cwd=worktree,
                    check=False, capture=True)
        if (dirty.stdout or "").strip():
            print(f"[sync] rollup: candidate worktree dirty after merge: "
                  f"{dirty.stdout.strip()[:400]}", file=sys.stderr)
            _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
            return None

        sha = run(["git", "rev-parse", "HEAD"], cwd=worktree,
                  capture=True).stdout.strip()
        print(f"[sync] rollup: candidate ready at {sha[:12]}")
        return RollupCandidate(worktree, temp_root, temp_branch, sha)
    except Exception:
        _remove_rollup_worktree(RollupCandidate(worktree, temp_root, temp_branch, ""))
        raise


def _push_rollup_candidate(candidate: RollupCandidate, rollup_branch: str) -> bool:
    env = os.environ.copy()
    env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
    with acquire_main_checkout_lock(timeout=120):
        run(["git", "fetch", "origin", rollup_branch],
            cwd=candidate.worktree, env=env, check=False, capture=True)
        push = run(["git", "push", "origin",
                    f"--force-with-lease=refs/heads/{rollup_branch}",
                    f"HEAD:refs/heads/{rollup_branch}"],
                   cwd=candidate.worktree, env=env, check=False, capture=True)
    if push.returncode != 0:
        print(f"[sync] rollup: push {rollup_branch} failed: "
              f"{((push.stdout or '') + (push.stderr or '')).strip()[:500]}",
              file=sys.stderr)
        return False
    print(f"[sync] rollup: pushed {rollup_branch} at {candidate.sha[:12]}")
    return True


def _open_rollup_pr(rollup_branch: str, source_branch: str,
                    target_branch: str) -> dict | None:
    if not _gh_available():
        print("[sync] rollup: gh CLI missing; skipping PR management")
        return None
    try:
        res = run(["gh", "pr", "list",
                   "--base", target_branch,
                   "--state", "open",
                   "--label", PR_LABEL,
                   "--json", "number,headRefName,headRefOid,mergeable,statusCheckRollup,title,createdAt",
                   "--limit", "100"],
                  capture=True, check=False)
        if res.returncode != 0:
            print(f"[sync] rollup: gh pr list failed: "
                  f"{((res.stdout or '') + (res.stderr or '')).strip()[:300]}",
                  file=sys.stderr)
            return None
        import json as _json
        rows = _json.loads(res.stdout or "[]")
    except Exception as exc:
        print(f"[sync] rollup: could not inspect PRs: {exc}", file=sys.stderr)
        return None
    for pr in rows if isinstance(rows, list) else []:
        if pr.get("headRefName") == rollup_branch:
            return pr
    return None


def _create_rollup_pr(rollup_branch: str, source_branch: str,
                      target_branch: str) -> bool:
    title = f"Roll up {source_branch} to {target_branch}"
    body = (
        f"Managed rollup PR from `{source_branch}` to `{target_branch}`.\n\n"
        f"`tools/sync_with_auto_dev.py` updates `{rollup_branch}` from "
        f"`origin/{target_branch}` plus a merge of `origin/{source_branch}`. "
        f"The PR is merged automatically once checks are green and GitHub "
        f"reports it mergeable."
    )
    cmd = ["gh", "pr", "create",
           "--base", target_branch,
           "--head", rollup_branch,
           "--title", title,
           "--body", body,
           "--label", PR_LABEL]
    res = run(cmd, capture=True, check=False)
    if res.returncode != 0:
        err = (res.stdout or "") + (res.stderr or "")
        if "label" in err.lower() and "not found" in err.lower():
            run(["gh", "label", "create", PR_LABEL,
                 "--description", "Automated branch rollup PR",
                 "--color", "0E8A16"],
                check=False, capture=True)
            res = run(cmd, capture=True, check=False)
    if res.returncode != 0:
        if _no_commits_between_error((res.stdout or "") + (res.stderr or "")):
            print(f"[sync] rollup: no-op; GitHub reports no commits between "
                  f"{target_branch} and {rollup_branch}")
            _delete_managed_rollup_branch_if_no_pr(rollup_branch, target_branch)
            return True
        print(f"[sync] rollup: gh pr create failed: "
              f"{((res.stdout or '') + (res.stderr or '')).strip()[:500]}",
              file=sys.stderr)
        return False
    print(f"[sync] rollup: opened PR from {rollup_branch} to {target_branch}")
    return True


def _merge_rollup_pr(pr: dict, rollup_branch: str, target_branch: str) -> bool:
    number = pr["number"]
    print(f"[sync] rollup: PR #{number} is green and mergeable; merging into {target_branch}")
    res = run(["gh", "pr", "merge", str(number),
               "--merge", "--delete-branch"],
              capture=True, check=False)
    if res.returncode != 0:
        print(f"[sync] rollup: gh pr merge failed: "
              f"{((res.stdout or '') + (res.stderr or '')).strip()[:500]}",
              file=sys.stderr)
        return False
    print(f"[sync] rollup: merged PR #{number}; deleted {rollup_branch}")
    return True


def sync_rollup_pr(source_branch: str, target_branch: str,
                   rollup_branch: str, *, no_push: bool) -> bool:
    print(f"[sync] rollup: source={source_branch} target={target_branch} branch={rollup_branch}")
    git("fetch", "origin", "--prune")
    if not has_remote_branch(source_branch):
        print(f"[sync] rollup: origin/{source_branch} missing", file=sys.stderr)
        return False
    if not has_remote_branch(target_branch):
        print(f"[sync] rollup: origin/{target_branch} missing", file=sys.stderr)
        return False
    target_sha = _origin_sha(target_branch)
    if target_sha is None:
        print(f"[sync] rollup: could not resolve origin/{target_branch}", file=sys.stderr)
        return False
    if _merge_base_contains(f"origin/{source_branch}", f"origin/{target_branch}"):
        print(f"[sync] rollup: no-op; origin/{source_branch} is already "
              f"included in origin/{target_branch} at {target_sha[:12]}")
        if not no_push:
            _delete_managed_rollup_branch_if_no_pr(rollup_branch, target_branch)
        return True

    if no_push:
        candidate = _build_rollup_candidate(source_branch, target_branch)
        if candidate is None:
            return False
        try:
            if candidate.sha == target_sha:
                print(f"[sync] rollup: no-op; candidate HEAD equals "
                      f"origin/{target_branch} at {target_sha[:12]}")
                return True
            print(f"[sync] rollup: no-push candidate {candidate.sha[:12]} constructed")
            return True
        finally:
            _remove_rollup_worktree(candidate)

    pr = _open_rollup_pr(rollup_branch, source_branch, target_branch)

    pr_age_hours = _hours_since(pr.get("createdAt") or "") if pr is not None else None
    action = _rollup_pr_action(pr, pr_age_hours)
    reason = _rollup_pr_action_reason(pr, pr_age_hours)
    if action == "merge":
        print(f"[sync] rollup: action=merge; {reason}")
        return _merge_rollup_pr(pr, rollup_branch, target_branch)
    if action == "wait":
        print(f"[sync] rollup: action=wait; {reason}")
        return True
    if action == "create":
        print(f"[sync] rollup: action=create; {reason}")
    else:
        print(f"[sync] rollup: action=rebuild; {reason}")

    candidate = _build_rollup_candidate(source_branch, target_branch)
    if candidate is None:
        return False
    try:
        if candidate.sha == target_sha:
            print(f"[sync] rollup: no-op; candidate HEAD equals "
                  f"origin/{target_branch} at {target_sha[:12]}")
            _delete_managed_rollup_branch_if_no_pr(rollup_branch, target_branch)
            return True
        if not _push_rollup_candidate(candidate, rollup_branch):
            return False
    finally:
        _remove_rollup_worktree(candidate)

    pr = _open_rollup_pr(rollup_branch, source_branch, target_branch)
    if pr is None:
        return _create_rollup_pr(rollup_branch, source_branch, target_branch)
    print(f"[sync] rollup: updated PR #{pr['number']} on {rollup_branch}")
    return True


def main():
    global SOURCE_BRANCH, MIRROR_BRANCH, UPSTREAM_BRANCH, PR_BRANCH

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-push", action="store_true",
                        help="Construct and validate the rollup candidate locally; do not push or manage PRs")
    parser.add_argument("--source-branch", default=None,
                        help="Source branch to roll up (default: host BEDC_PIPELINE_BRANCH or codex-auto-dev)")
    parser.add_argument("--target-branch", default=None,
                        help="Target branch / PR base (default: host BEDC_ROLLUP_TARGET_BRANCH or dev)")
    parser.add_argument("--upstream-branch", default=None,
                        help="Alias for --target-branch kept for compatibility")
    parser.add_argument("--mirror-branch", default=None,
                        help="Compatibility option; ignored by the rollup flow")
    parser.add_argument("--rollup-branch", default=None,
                        help="Managed PR branch name (default: rollup-<source>-to-<target>)")
    args = parser.parse_args()

    SOURCE_BRANCH = args.source_branch if args.source_branch is not None else _source_branch_default()
    target_arg = args.target_branch if args.target_branch is not None else args.upstream_branch
    UPSTREAM_BRANCH = target_arg if target_arg is not None else _upstream_branch_default()
    if args.mirror_branch is not None:
        MIRROR_BRANCH = args.mirror_branch
    PR_BRANCH = args.rollup_branch or _rollup_branch_name(SOURCE_BRANCH, UPSTREAM_BRANCH)

    ok = sync_rollup_pr(SOURCE_BRANCH, UPSTREAM_BRANCH, PR_BRANCH,
                        no_push=args.no_push)
    if not ok:
        sys.exit(2)


PR_LABEL = "auto-dev-sync"
PR_BRANCH_PREFIX = "auto-dev-sync"
PR_BRANCH = f"{PR_BRANCH_PREFIX}-current"
PR_AGE_THRESHOLD_HOURS = 24
# A non-green catch-up PR open past this many hours is moved onto
# the current auto-dev tip when auto-dev has advanced past its head. The
# sync daemon re-execs this script each cycle, so env overrides take effect
# without a daemon restart.
try:
    PR_REPLACE_OPEN_HOURS = float(os.environ.get("BEDC_PR_REPLACE_OPEN_HOURS", "6"))
except (TypeError, ValueError):
    PR_REPLACE_OPEN_HOURS = 6.0


def _gh_available() -> bool:
    return shutil.which("gh") is not None


def _origin_commit_iso(ref: str) -> str | None:
    try:
        res = run(["git", "log", "-1", "--format=%aI", f"origin/{ref}"],
                  capture=True, check=False)
        if res.returncode != 0:
            return None
        return res.stdout.strip() or None
    except Exception:
        return None


def _hours_since(iso_str: str) -> float | None:
    """Return hours between iso_str (with timezone) and now (UTC)."""
    try:
        # python 3.11+ has datetime.fromisoformat that accepts trailing offsets.
        # Older Pythons get a manual reparse via email.utils.
        try:
            from datetime import datetime, timezone
            # gh emits a trailing 'Z' (e.g. 2026-05-29T17:23:21Z); Python's
            # datetime.fromisoformat only accepts that on 3.11+. Normalize so
            # the parse works on 3.9/3.10 too — otherwise this returns None for
            # every gh createdAt and the age-box PR-replace path never fires.
            iso_norm = iso_str.strip()
            if iso_norm.endswith(("Z", "z")):
                iso_norm = iso_norm[:-1] + "+00:00"
            dt = datetime.fromisoformat(iso_norm)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            from datetime import datetime as _dt
            now = _dt.now(timezone.utc)
            return (now - dt).total_seconds() / 3600.0
        except Exception:
            return None
    except Exception:
        return None


def _open_sync_prs() -> list[dict]:
    """Return open PRs base=dev with the auto-sync label."""
    try:
        res = run(["gh", "pr", "list",
                   "--base", UPSTREAM_BRANCH,
                   "--state", "open",
                   "--label", PR_LABEL,
                   "--json", "number,headRefName,headRefOid,mergeable,statusCheckRollup,title,createdAt",
                   "--limit", "100"],
                  capture=True, check=False)
        if res.returncode != 0:
            return []
        import json as _json
        rows = _json.loads(res.stdout or "[]")
        return rows if isinstance(rows, list) else []
    except Exception:
        return []


def _active_catchup_pr(open_prs: list[dict]) -> dict | None:
    for pr in open_prs:
        if pr.get("headRefName") == PR_BRANCH:
            return pr
    return None


def _close_sync_pr(pr: dict, *, comment: str, delete_branch: bool) -> bool:
    number = pr["number"]
    head_ref = pr.get("headRefName")
    close = run(["gh", "pr", "close", str(number), "--comment", comment],
                capture=True, check=False)
    if close.returncode != 0:
        print(f"[sync] dev-catchup: close PR #{number} failed: "
              f"{((close.stdout or '') + (close.stderr or '')).strip()[:300]}")
        return False
    if delete_branch and head_ref:
        delete = run(["git", "push", "origin", "--delete", head_ref],
                     capture=True, check=False)
        if delete.returncode != 0:
            print(f"[sync] dev-catchup: delete branch {head_ref} failed: "
                  f"{((delete.stdout or '') + (delete.stderr or '')).strip()[:300]}")
    print(f"[sync] dev-catchup: closed PR #{number}")
    return True


def _close_non_active_sync_prs(open_prs: list[dict], active_pr: dict | None) -> int:
    active_number = active_pr.get("number") if active_pr else None
    head = _origin_sha(MIRROR_BRANCH) or f"origin/{MIRROR_BRANCH}"
    comment = (
        f"Closed by the managed catch-up branch `{PR_BRANCH}` at {head}. "
        f"The sync daemon keeps at most one active `{PR_LABEL}` PR."
    )
    closed = 0
    for pr in open_prs:
        if pr.get("number") == active_number:
            continue
        head_ref = pr.get("headRefName")
        if _close_sync_pr(pr, comment=comment, delete_branch=(head_ref != PR_BRANCH)):
            closed += 1
    return closed


def _push_catchup_branch(branch: str = PR_BRANCH) -> bool:
    try:
        run(["git", "fetch", "origin",
             f"refs/heads/{MIRROR_BRANCH}:refs/remotes/origin/{MIRROR_BRANCH}"],
            check=False, capture=True)
        push = run(["git", "push", "origin", "--force",
                    f"refs/remotes/origin/{MIRROR_BRANCH}:refs/heads/{branch}"],
                   check=False, capture=True)
        if push.returncode != 0:
            print(f"[sync] dev-catchup: push branch {branch} failed: "
                  f"{((push.stdout or '') + (push.stderr or '')).strip()[:400]}")
            return False
        return True
    except Exception as exc:
        print(f"[sync] dev-catchup: push branch {branch} failed: {exc}")
        return False


def _create_catchup_pr(branch: str, reasons: list[str]) -> bool:
    body = (
        f"Automated catch-up PR from `{MIRROR_BRANCH}` to `{UPSTREAM_BRANCH}`.\n\n"
        f"Trigger: {'; '.join(reasons)}.\n\n"
        f"This PR is managed by `tools/sync_with_auto_dev.py` and will be "
        f"auto-merged once all required checks pass. Later sync cycles "
        f"move `{branch}` to the current `{MIRROR_BRANCH}` tip, so "
        f"the same PR tracks the current catch-up candidate."
    )
    title = f"Sync {MIRROR_BRANCH} to {UPSTREAM_BRANCH}"
    cmd = ["gh", "pr", "create",
           "--base", UPSTREAM_BRANCH,
           "--head", branch,
           "--title", title,
           "--body", body,
           "--label", PR_LABEL]
    r = run(cmd, capture=True, check=False)
    if r.returncode != 0:
        # If the label doesn't exist yet, create it then retry once.
        err = (r.stdout or "") + (r.stderr or "")
        if "label" in err.lower() and "not found" in err.lower():
            run(["gh", "label", "create", PR_LABEL,
                 "--description", "Automated dev<-auto-dev sync PR",
                 "--color", "0E8A16"],
                check=False, capture=True)
            r = run(cmd, capture=True, check=False)
        if r.returncode != 0:
            print(f"[sync] dev-catchup: gh pr create failed: "
                  f"{((r.stdout or '') + (r.stderr or ''))[:400]}")
            return False
    print(f"[sync] dev-catchup: opened PR via branch {branch}")
    return True


def _format_pr_wait_state(pr: dict) -> str:
    open_age = _hours_since(pr.get("createdAt") or "")
    age_txt = f"{open_age:.1f}h" if open_age is not None else "?"
    failed = "failed" if _pr_has_failed_check(pr) else "pending"
    return f"PR #{pr['number']} open {age_txt} ({failed})"


def _dev_catchup_needed(force_open_pr: bool, reasons: list[str]) -> bool:
    dev_iso = _origin_commit_iso(UPSTREAM_BRANCH)
    age_hours = _hours_since(dev_iso) if dev_iso else None

    try:
        ahead = run(
            ["git", "rev-list", "--count",
             f"origin/{UPSTREAM_BRANCH}..origin/{MIRROR_BRANCH}"],
            capture=True, check=False).stdout.strip()
        ahead_count = int(ahead) if ahead.isdigit() else 0
    except Exception:
        ahead_count = 0

    if ahead_count <= 0:
        return False
    if force_open_pr:
        reasons.append(f"auto-dev ahead of dev by {ahead_count} commit(s)")
        return True
    if age_hours is not None and age_hours >= PR_AGE_THRESHOLD_HOURS:
        reasons.append(f"dev last commit {age_hours:.1f}h ago "
                       f"(threshold {PR_AGE_THRESHOLD_HOURS}h)")
        return True
    if age_hours is not None and age_hours >= 6:
        reasons.append(f"auto-dev ahead of dev by {ahead_count} commit(s)")
        return True
    return False


def _all_checks_green(pr: dict) -> bool:
    """Return True iff every required check passed and PR is mergeable."""
    if pr.get("mergeable") != "MERGEABLE":
        return False
    rollup = pr.get("statusCheckRollup") or []
    if not rollup:
        return False
    for check in rollup:
        # GitHub API returns either CheckRun (with conclusion) or
        # StatusContext (with state). Treat anything not in the success
        # set as not-yet-green.
        conclusion = check.get("conclusion") or check.get("state") or ""
        if conclusion.upper() not in ("SUCCESS", "NEUTRAL", "SKIPPED"):
            return False
    return True


def _pr_has_failed_check(pr: dict) -> bool:
    """Return True if any PR check has a terminal failure state."""
    rollup = pr.get("statusCheckRollup") or []
    failed = {
        "ACTION_REQUIRED",
        "ERROR",
        "FAILURE",
        "FAILED",
        "STARTUP_FAILURE",
        "TIMED_OUT",
    }
    for check in rollup:
        conclusion = (check.get("conclusion") or check.get("state") or "").upper()
        if conclusion in failed:
            return True
    return False


def _rollup_pr_action(pr: dict | None, pr_age_hours: float | None) -> str:
    if pr is None:
        return "create"
    if _all_checks_green(pr):
        return "merge"
    if pr.get("mergeable") == "CONFLICTING":
        return "rebuild"
    if _pr_has_failed_check(pr):
        return "rebuild"
    if pr_age_hours is not None and pr_age_hours > PR_REPLACE_OPEN_HOURS:
        return "rebuild"
    return "wait"


def _rollup_pr_action_reason(pr: dict | None, pr_age_hours: float | None) -> str:
    if pr is None:
        return "no managed rollup PR is open"
    number = pr.get("number", "?")
    age = f"{pr_age_hours:.1f}h" if pr_age_hours is not None else "unknown age"
    if _all_checks_green(pr):
        return f"PR #{number} is green and mergeable"
    if pr.get("mergeable") == "CONFLICTING":
        return f"PR #{number} is conflicting"
    if _pr_has_failed_check(pr):
        return f"PR #{number} has a failed check"
    if pr_age_hours is not None and pr_age_hours > PR_REPLACE_OPEN_HOURS:
        return (f"PR #{number} is non-green after {age} "
                f"(threshold {PR_REPLACE_OPEN_HOURS:.1f}h)")
    return f"PR #{number} is non-green ({age}); leaving candidate in place"


def _auto_dev_advanced_past(pr_head: str | None) -> int:
    """Return commit count from PR head to current origin/auto-dev."""
    if not pr_head:
        return 0
    return _rev_list_count(f"{pr_head}..origin/{MIRROR_BRANCH}")


def sync_dev_catchup_pr() -> None:
    """Open / auto-merge a managed auto-dev catch-up PR back into dev.

    Trigger condition: origin/dev last commit older than threshold OR
    auto-dev/dev histories have diverged (not a pure ff descendant).

    Idempotent: at most one active open PR with PR_LABEL exists at a time.
    """
    if not _gh_available():
        print("[sync] dev-catchup: gh CLI missing; skipping")
        return
    if not has_remote_branch(UPSTREAM_BRANCH):
        return

    # Phase A: keep one managed PR and close all other labeled open PRs.
    open_prs = _open_sync_prs()
    pr = _active_catchup_pr(open_prs)
    closed_pr_count = _close_non_active_sync_prs(open_prs, pr)

    reasons = []
    if pr is not None:
        if _all_checks_green(pr):
            number = pr["number"]
            head_ref = pr["headRefName"]
            print(f"[sync] dev-catchup: PR #{number} all green; "
                  f"auto-merging + deleting {head_ref}")
            r = run(["gh", "pr", "merge", str(number),
                     "--merge", "--delete-branch"],
                    capture=True, check=False)
            if r.returncode != 0:
                print(f"[sync] dev-catchup: gh pr merge failed: "
                      f"{(r.stdout or '') + (r.stderr or '')[:300]}")
            else:
                print(f"[sync] dev-catchup: PR #{number} merged "
                      f"into {UPSTREAM_BRANCH}; branch {head_ref} deleted")
            return

        # Not green. Keep the same PR and move its branch to current auto-dev.
        pr_head = pr.get("headRefOid")
        advanced_by = _auto_dev_advanced_past(pr_head)
        open_age = _hours_since(pr.get("createdAt") or "")

        if advanced_by > 0:
            if _push_catchup_branch(PR_BRANCH):
                print(f"[sync] dev-catchup: moved PR #{pr['number']} "
                      f"on {PR_BRANCH}; {MIRROR_BRANCH} advanced "
                      f"{advanced_by} commit(s)")
            return

        if open_age is not None and open_age >= PR_REPLACE_OPEN_HOURS:
            print(f"[sync] dev-catchup: {_format_pr_wait_state(pr)}; "
                  f"{MIRROR_BRANCH} has not advanced past PR head")
            return

        print(f"[sync] dev-catchup: {_format_pr_wait_state(pr)}; leaving "
              f"managed PR in place")
        return

    # Phase B: no active PR. Check whether one is needed.
    if not _dev_catchup_needed(closed_pr_count > 0, reasons):
        return

    # Phase C: create or update the fixed branch + PR.
    branch = PR_BRANCH
    print(f"[sync] dev-catchup: opening PR — {'; '.join(reasons)}")
    if not _push_catchup_branch(branch):
        return
    _create_catchup_pr(branch, reasons)


if __name__ == "__main__":
    main()

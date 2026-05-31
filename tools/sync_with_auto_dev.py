#!/usr/bin/env python3
"""Three-branch sync between `dev` (external upstream), `auto-dev`
(stable mirror) and `codex-auto-dev` (pipeline integration). Run
periodically by the sync daemon (every 600s by default) so the three
branches converge.

Flow:
  1. fetch origin (all branches)
  2. on `auto-dev`: merge `origin/dev` (NEW — pulls external user /
     supervisor commits into the mirror; codex resolves on conflict)
  3. on `codex-auto-dev`: merge `origin/auto-dev` (now contains dev's
     content); codex resolves on conflict
  4. on `auto-dev` (again): merge `codex-auto-dev` (mirror pipeline
     output); codex resolves on conflict
  5. push all three branches that received commits
  6. checkout back to the branch the user started on

Both merges use `git merge --no-ff --no-edit` (no rebase). On conflict,
codex is invoked inside the worktree with a generic resolve prompt;
codex is expected to resolve, `git add`, and `git commit --no-edit`. If
codex cannot resolve, the merge is aborted and the script exits non-zero.

Working-tree dirty state is stashed (`git stash -u`) and restored after
the sync completes, including across the branch switches.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
import tempfile
from pathlib import Path

from host_context import load_host_context

_HOST_CONTEXT = load_host_context(
    repo_root=Path(__file__).resolve().parent.parent,
    defaults={
        "INTEGRATION_BRANCH": "codex-auto-dev",
        "MIRROR_BRANCH": "auto-dev",
        "REVIEW_BASE_BRANCH": "dev",
        "SYNC_VALIDATION_WORKTREE": "/tmp/.bedc_sync_validate_wt",
    },
)
REPO_ROOT = _HOST_CONTEXT.path("REPO_ROOT")
SOURCE_BRANCH = _HOST_CONTEXT.require("INTEGRATION_BRANCH")
MIRROR_BRANCH = _HOST_CONTEXT.require("MIRROR_BRANCH")
UPSTREAM_BRANCH = _HOST_CONTEXT.require("REVIEW_BASE_BRANCH")
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
VALIDATION_WORKTREE = _HOST_CONTEXT.path("SYNC_VALIDATION_WORKTREE")
VALIDATION_BRANCH = "bedc-sync-validate"
CONFLICT_PROMPT = """You are resolving git merge conflicts in the BEDC mathematics project.

The merge currently has unresolved conflicts. Files with `<<<<<<<` / `=======` / `>>>>>>>` markers:
{conflicted}

## Repository conventions

- `lean4/BEDC/**.lean`: when both sides added theorems / definitions / imports, keep the union. For genuinely incompatible signatures, keep the more substantive version (longer body, more named hypotheses, more BHist anchors).
- `papers/bedc/parts/**.tex`: both sides may have added `\\input{...}` lines, `\\leanchecked{...}` markers, theorems, definitions. Keep the union when content is additive. For LaTeX `\\label{...}` collisions, keep ONE copy (drop the duplicate label entirely; do not rename).
- `lean4/scripts/**` / `papers/bedc/scripts/**` / `*.py` / `*.sh`: prefer the side with newer behaviour (more recent commit, longer body, additional code paths). Read both sides' diffs before deciding.
- `MEMORY.md` / `CLAUDE.md` / `AGENTS.md` / `SKILL.md`: keep the union of bullet points / sections; if the same key was edited differently on both sides, keep the more specific / more recent version.

## Process

For each conflicted file:
1. `git diff :2:<path>` and `git diff :3:<path>` to see HEAD's vs incoming version.
2. Resolve manually (edit the file to drop conflict markers + chosen content).
3. After all files resolved: run `bash papers/bedc/scripts/check_tex_size.sh` (must exit 0) and `cd lean4&& lake build` if any `.lean` file was touched (must succeed).
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
    from repo_push_lock import acquire_push_lock  # tools/ is on sys.path

    return acquire_push_lock(SOURCE_BRANCH, timeout=timeout)


def current_branch() -> str:
    return git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()


def working_tree_dirty() -> bool:
    out = git("status", "--porcelain", capture=True).stdout
    return bool(out.strip())


def conflicted_files() -> list[str]:
    out = git("diff", "--name-only", "--diff-filter=U", capture=True).stdout
    return [line for line in out.splitlines() if line]


def has_conflict_markers(path: str) -> bool:
    try:
        text = (REPO_ROOT / path).read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return True
    return any(marker in text for marker in ("<<<<<<<", "=======", ">>>>>>>"))


def write_locked_git_wrapper(wrapper_dir: Path) -> dict[str, str]:
    real_git = shutil.which("git") or "/usr/bin/git"
    tools_path = str(REPO_ROOT / "tools")
    wrapper = wrapper_dir / "git"
    wrapper.write_text(
        "#!/usr/bin/env python3\n"
        "import os\n"
        "import subprocess\n"
        "import sys\n"
        f"sys.path.insert(0, {tools_path!r})\n"
        "from repo_push_lock import acquire_push_lock\n"
        f"REAL_GIT = {real_git!r}\n"
        f"BRANCH = {SOURCE_BRANCH!r}\n"
        "WRITE_CMDS = {'add', 'commit', 'reset', 'checkout', 'merge', 'pull', 'stash', 'push'}\n"
        "argv = sys.argv[1:]\n"
        "cmd = argv[0] if argv else ''\n"
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


def call_codex_to_resolve(work_dir: Path, timeout: int = 1800) -> bool:
    """Invoke codex inside `work_dir` to resolve current merge conflicts.

    Returns True if codex completed and the merge has no remaining conflicts;
    False otherwise (caller should `git merge --abort`)."""
    files = conflicted_files()
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

    unresolved = [path for path in files if has_conflict_markers(path)]
    if unresolved:
        print(f"[sync] codex left conflict markers: {unresolved}", file=sys.stderr)
        return False
    with acquire_main_checkout_lock(timeout=120):
        merge_head = (REPO_ROOT / ".git" / "MERGE_HEAD").exists()
        if merge_head:
            git("add", "--", *files)
            remaining = conflicted_files()
            if remaining:
                print(f"[sync] codex left unresolved index conflicts: {remaining}", file=sys.stderr)
                return False
            git("commit", "--no-edit")
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


def merge_with_codex_fallback(target: str, label: str) -> bool:
    """Merge `target` into HEAD. On conflict, invoke codex once. Returns True on success."""
    print(f"[sync] {label}: merging {target}...")
    with acquire_main_checkout_lock(timeout=120):
        res = git("merge", "--no-ff", "--no-edit", target, check=False, capture=True)
    if res.returncode == 0:
        print(f"[sync] {label}: merge clean")
        return True

    # Non-zero: either no-op (already up to date) or conflict.
    out = (res.stdout or "") + (res.stderr or "")
    if "Already up to date" in out or "already up to date" in out:
        print(f"[sync] {label}: already up to date")
        return True

    if not conflicted_files():
        # Some other failure (e.g. dirty WT). Surface it.
        print(f"[sync] {label}: merge failed without conflicts:\n{out}", file=sys.stderr)
        return False

    if not call_codex_to_resolve(REPO_ROOT):
        print(f"[sync] {label}: codex could not resolve; aborting merge", file=sys.stderr)
        with acquire_main_checkout_lock(timeout=120):
            git("merge", "--abort", check=False)
        return False

    print(f"[sync] {label}: codex resolved conflicts and committed")
    return True


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
            merge = git("merge", "--no-ff", "--no-edit", f"origin/{branch}",
                        check=False, capture=True)
        if merge.returncode != 0:
            # Merge conflict or other error — abort and let outer loop
            # handle (codex conflict resolver path).
            with acquire_main_checkout_lock(timeout=120):
                git("merge", "--abort", check=False, capture=True)
            print(f"[sync] push retry remerge had conflict; aborting retry",
                  file=sys.stderr)
            return last_rc
    return last_rc


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
    if VALIDATION_WORKTREE.exists():
        res = git("worktree", "remove", "--force", str(VALIDATION_WORKTREE),
                  check=False, capture=True)
        if res.returncode != 0:
            print(f"[sync] dev->auto-dev validation: could not remove old "
                  f"worktree: {((res.stdout or '') + (res.stderr or '')).strip()[:200]}")


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

    merge = run(["git", "merge", "--no-ff", "--no-edit", dev_sha],
                cwd=VALIDATION_WORKTREE, check=False, capture=True)
    if merge.returncode != 0:
        run(["git", "merge", "--abort"], cwd=VALIDATION_WORKTREE,
            check=False, capture=True)
        print(f"[sync] dev->auto-dev validation: merge failed rc={merge.returncode}")
        return False, dev_sha, mirror_sha

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
            merge = git("merge", "--no-ff", "--no-edit", dev_sha,
                        check=False, capture=True)
            if merge.returncode != 0:
                git("merge", "--abort", check=False, capture=True)
                print("[sync] dev->auto-dev: validated merge failed in main checkout; retry next cycle")
                return False
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


def main():
    global SOURCE_BRANCH, MIRROR_BRANCH, UPSTREAM_BRANCH

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-push", action="store_true",
                        help="Skip the two pushes to origin (still does the merges locally)")
    parser.add_argument("--source-branch", default=SOURCE_BRANCH,
                        help=f"Pipeline integration branch (default: {SOURCE_BRANCH})")
    parser.add_argument("--mirror-branch", default=MIRROR_BRANCH,
                        help=f"Stable mirror branch (default: {MIRROR_BRANCH})")
    parser.add_argument("--upstream-branch", default=UPSTREAM_BRANCH,
                        help=f"Review base branch (default: {UPSTREAM_BRANCH})")
    args = parser.parse_args()
    SOURCE_BRANCH = args.source_branch
    MIRROR_BRANCH = args.mirror_branch
    UPSTREAM_BRANCH = args.upstream_branch

    original = current_branch()

    # Always fetch every ref from origin so both branches' remote state is
    # current before we attempt local merges.
    git("fetch", "origin", "--prune")

    # Working-tree dirty: stash with -u so untracked files come along.
    # Capture the EXACT stash commit OID we create. Restore must touch only
    # THIS stash, never `stash@{0}` — the git stash stack is shared across
    # all worktrees, so a bare `git stash pop` can pop a sibling worker's or
    # another daemon's stash (the `recovered-non-R4851-...-from-stash-pop`
    # stash on the stack is hard evidence this happened).
    stashed = False
    stash_oid = None
    if working_tree_dirty():
        print("[sync] working tree dirty; stashing with -u")
        try:
            with acquire_main_checkout_lock(timeout=120):
                git("stash", "push", "-u", "-m", f"sync_with_auto_dev autostash {os.getpid()}")
                res = git("rev-parse", "--verify", "--quiet", "stash@{0}",
                          check=False, capture=True)
        except TimeoutError as exc:
            print(f"[sync] push lock timeout while stashing dirty tree: {exc}",
                  file=sys.stderr)
            return
        stash_oid = res.stdout.strip() if res.returncode == 0 else None
        stashed = True

    success = True
    try:
        # Step 1 (mirror, runs FIRST): auto-dev <- codex-auto-dev
        # The cheap, must-always-run mirror that keeps the stable branch
        # tracking pipeline output. Its content is already gated per round,
        # so it merges in seconds. Run it BEFORE the expensive external-dev
        # validation below so a slow/timing-out dev merge can never starve
        # it (observed 2026-05-29: auto-dev fell 768 commits / ~12h behind
        # because the 1800s dev-validation lake build timed out every tick
        # and the old Step-0-first ordering gated the mirror behind it).
        if not sync_one_direction(MIRROR_BRANCH, SOURCE_BRANCH,
                                  no_push=args.no_push):
            success = False
            return

        # Step 2: codex-auto-dev <- auto-dev
        # Pull auto-dev (which carries any external dev content merged in by
        # a prior tick's Step 3) into the pipeline integration branch so
        # codex workers see it on next round dispatch.
        if not sync_one_direction(SOURCE_BRANCH, f"origin/{MIRROR_BRANCH}",
                                  no_push=args.no_push):
            success = False
            return

        # Step 3 (external upstream, runs LAST): auto-dev <- origin/dev
        # Pull external user / supervisor commits from `dev` into the stable
        # mirror. Gated by a scratch-worktree lake build that commonly times
        # out (1800s) under pipeline load. Run LAST and treat failure as
        # NON-FATAL: the mirror above already converged this tick, so a
        # timeout here only delays external dev content by one tick — it
        # never starves auto-dev. dev content reaches the pipeline on the
        # next tick whose validation passes (Step 2). Only bail if the
        # failed dev merge left the main checkout dirty (in-checkout merge
        # conflict that needs careful handling).
        if has_remote_branch(UPSTREAM_BRANCH):
            if not sync_dev_to_auto_dev_validated(no_push=args.no_push):
                if working_tree_dirty():
                    print("[sync] dev -> auto-dev failed AND working tree "
                          "dirty; bailing this tick for safety")
                    success = False
                    return
                print("[sync] dev -> auto-dev validation failed (likely "
                      "lake-build timeout); mirror already converged this "
                      "tick, external dev content waits for next passing tick")
        else:
            print(f"[sync] origin/{UPSTREAM_BRANCH} missing; skipping dev → auto-dev step")
    finally:
        # Always switch back to the branch the user started on.
        if original != current_branch():
            print(f"[sync] switching back to {original}")
            try:
                with acquire_main_checkout_lock(timeout=120):
                    git("checkout", original, check=False)
            except TimeoutError as exc:
                print(f"[sync] push lock timeout while switching back to {original}: {exc}",
                      file=sys.stderr)
        if stashed:
            _restore_autostash(stash_oid)

    if success:
        print(f"[sync] done: {SOURCE_BRANCH} <-> {MIRROR_BRANCH} converged "
              f"(both pushed)" if not args.no_push else "(no-push)")
    else:
        sys.exit(2)

    # Step 4: dev catch-up PR.
    # When dev lags auto-dev by ≥1 day (or has diverged history),
    # cut a branch from origin/auto-dev, open a PR targeting dev, and
    # auto-merge once CI is green. Idempotent — skips when an existing
    # open PR with the auto-sync label already covers this state.
    if success and not args.no_push:
        try:
            sync_dev_catchup_pr()
        except Exception as exc:
            print(f"[sync] dev catch-up step failed (non-fatal): {exc}")


PR_LABEL = "auto-dev-sync"
PR_BRANCH_PREFIX = "auto-dev-sync"
PR_AGE_THRESHOLD_HOURS = 24
# An un-merged catch-up PR open past this many hours is closed and reopened
# on the current auto-dev tip, regardless of pending/failed check state, as
# long as auto-dev has advanced past its head. auto-dev produces commits
# continuously, so a stale PR head never lands on its own — the only way the
# catch-up PR stays fresh is to time-box it. Env-overridable (no restart;
# the sync daemon re-execs this script each cycle) to match the rest of the
# daemon knobs (AUTO_HEAL_INTERVAL_SECONDS etc.).
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


def _existing_open_pr() -> dict | None:
    """Return the first open PR base=dev with our auto-sync label, else None."""
    try:
        res = run(["gh", "pr", "list",
                   "--base", UPSTREAM_BRANCH,
                   "--state", "open",
                   "--label", PR_LABEL,
                   "--json", "number,headRefName,headRefOid,mergeable,statusCheckRollup,title,createdAt",
                   "--limit", "5"],
                  capture=True, check=False)
        if res.returncode != 0:
            return None
        import json as _json
        rows = _json.loads(res.stdout or "[]")
        return rows[0] if rows else None
    except Exception:
        return None


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
    """Return True if any PR check has a terminal failure/cancelled state."""
    rollup = pr.get("statusCheckRollup") or []
    failed = {
        "ACTION_REQUIRED",
        "CANCELLED",
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


def _auto_dev_advanced_past(pr_head: str | None) -> int:
    """Return commit count from PR head to current origin/auto-dev."""
    if not pr_head:
        return 0
    return _rev_list_count(f"{pr_head}..origin/{MIRROR_BRANCH}")


def _close_stale_pr(pr: dict, advanced_by: int) -> bool:
    number = pr["number"]
    head_ref = pr.get("headRefName")
    head = _origin_sha(MIRROR_BRANCH) or "current auto-dev HEAD"
    comment = (
        f"Superseded by fresh auto-dev HEAD {head} "
        f"({advanced_by} commit(s) past this PR head)."
    )
    close = run(["gh", "pr", "close", str(number), "--comment", comment],
                capture=True, check=False)
    if close.returncode != 0:
        print(f"[sync] dev-catchup: close stale PR #{number} failed: "
              f"{((close.stdout or '') + (close.stderr or '')).strip()[:300]}")
        return False
    if head_ref:
        delete = run(["git", "push", "origin", "--delete", head_ref],
                     capture=True, check=False)
        if delete.returncode != 0:
            print(f"[sync] dev-catchup: delete stale branch {head_ref} failed: "
                  f"{((delete.stdout or '') + (delete.stderr or '')).strip()[:300]}")
    print(f"[sync] dev-catchup: closed stale PR #{number}; opening a fresh one")
    return True


def sync_dev_catchup_pr() -> None:
    """Open / auto-merge a PR from a fresh auto-dev branch back into dev.

    Trigger condition: origin/dev last commit older than threshold OR
    auto-dev/dev histories have diverged (not a pure ff descendant).

    Idempotent: at most one open PR with PR_LABEL exists at a time.
    """
    if not _gh_available():
        print("[sync] dev-catchup: gh CLI missing; skipping")
        return
    if not has_remote_branch(UPSTREAM_BRANCH):
        return

    # Phase A: handle any existing open PR (merge if green, replace if stale).
    pr = _existing_open_pr()
    force_open_pr = False
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

        # Not green. Decide whether to replace it with a fresh PR.
        pr_head = pr.get("headRefOid")
        advanced_by = _auto_dev_advanced_past(pr_head)
        open_age = _hours_since(pr.get("createdAt") or "")

        # (a) Failed checks + auto-dev has new commits → close and reopen
        #     immediately on the fresh tip to try again. We do NOT wait for
        #     the auto-dev HEAD to be green: the whole point of reopening is
        #     to retry with newer content, and this giant library rarely
        #     shows an all-green HEAD, so gating on it would strand the PR.
        if _pr_has_failed_check(pr) and advanced_by > 0:
            if not _close_stale_pr(pr, advanced_by):
                return
            force_open_pr = True
            reasons.append(f"failed PR superseded by {MIRROR_BRANCH} "
                           f"advancing {advanced_by} commit(s)")
        # (b) Age-box the stuck-pending case: a PR whose checks never resolve
        #     (perpetually pending, never flips to a failure conclusion) is
        #     replaced once it has been open past PR_REPLACE_OPEN_HOURS and
        #     auto-dev has moved past its head.
        elif (open_age is not None and open_age >= PR_REPLACE_OPEN_HOURS
                and advanced_by > 0):
            if not _close_stale_pr(pr, advanced_by):
                return
            force_open_pr = True
            reasons.append(f"PR open {open_age:.1f}h without merge "
                           f"(threshold {PR_REPLACE_OPEN_HOURS}h); "
                           f"{MIRROR_BRANCH} advanced {advanced_by} commit(s)")
        else:
            age_txt = f"{open_age:.1f}h" if open_age is not None else "?"
            failed = "failed" if _pr_has_failed_check(pr) else "pending"
            print(f"[sync] dev-catchup: PR #{pr['number']} open {age_txt} "
                  f"({failed}) — leaving in place "
                  f"({MIRROR_BRANCH} not ahead, or pending & < "
                  f"{PR_REPLACE_OPEN_HOURS}h)")
            return

    # Phase B: no open PR. Check whether one is needed.
    dev_iso = _origin_commit_iso(UPSTREAM_BRANCH)
    age_hours = _hours_since(dev_iso) if dev_iso else None

    # Divergence check: are there commits on auto-dev not on dev?
    try:
        ahead = run(
            ["git", "rev-list", "--count",
             f"origin/{UPSTREAM_BRANCH}..origin/{MIRROR_BRANCH}"],
            capture=True, check=False).stdout.strip()
        ahead_count = int(ahead) if ahead.isdigit() else 0
    except Exception:
        ahead_count = 0

    needs_pr = force_open_pr
    if age_hours is not None and age_hours >= PR_AGE_THRESHOLD_HOURS:
        needs_pr = True
        reasons.append(f"dev last commit {age_hours:.1f}h ago "
                       f"(threshold {PR_AGE_THRESHOLD_HOURS}h)")
    if ahead_count > 0 and age_hours is not None and age_hours >= 6:
        # Lower bar (6h) once divergence exists — still want to land
        # large pipeline outputs before they grow into thousands of
        # commits, even if dev is technically less than 1 day old.
        if not needs_pr:
            needs_pr = True
        reasons.append(f"auto-dev ahead of dev by {ahead_count} commit(s)")

    if not needs_pr:
        return

    # Phase C: create branch + PR.
    import datetime as _dt
    stamp = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%d-%H%M")
    branch = f"{PR_BRANCH_PREFIX}-{stamp}"
    print(f"[sync] dev-catchup: opening PR — {'; '.join(reasons)}")
    # Push origin/auto-dev as branch name (cheap — same SHA).
    try:
        run(["git", "fetch", "origin",
             f"refs/heads/{MIRROR_BRANCH}:refs/remotes/origin/{MIRROR_BRANCH}"],
            check=False, capture=True)
        run(["git", "push", "origin",
             f"refs/remotes/origin/{MIRROR_BRANCH}:refs/heads/{branch}"],
            check=False, capture=True)
    except Exception as exc:
        print(f"[sync] dev-catchup: push branch {branch} failed: {exc}")
        return

    body = (
        f"Automated catch-up PR from `{MIRROR_BRANCH}` to `{UPSTREAM_BRANCH}`.\n\n"
        f"Trigger: {'; '.join(reasons)}.\n\n"
        f"This PR is created by `tools/sync_with_auto_dev.py` and will be "
        f"auto-merged once all required checks pass (subsequent sync cycle "
        f"checks status; deletes the branch on merge). The pipeline mirrors "
        f"`{UPSTREAM_BRANCH}` back into `{MIRROR_BRANCH}` continuously, so "
        f"this only carries content that already lived on `{MIRROR_BRANCH}`."
    )
    title = f"Sync {MIRROR_BRANCH} → {UPSTREAM_BRANCH} ({stamp})"
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
            return
    print(f"[sync] dev-catchup: opened PR via branch {branch}")


if __name__ == "__main__":
    main()

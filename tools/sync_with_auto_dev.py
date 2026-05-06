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
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE_BRANCH = "codex-auto-dev"   # pipeline output (codex workers)
MIRROR_BRANCH = "auto-dev"          # stable mirror
UPSTREAM_BRANCH = "dev"             # external main branch (user / external commits)
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
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
4. `git add <each-file>` for each resolved file.
5. `git commit --no-edit` to finalize the merge. Do NOT amend.
6. Do NOT `git push`.

If you cannot resolve a conflict (genuinely incompatible semantic intent, build fails after resolution, etc.), run `git merge --abort` and explain in your final message what blocked the resolution.
"""


def run(cmd, *, cwd=REPO_ROOT, check=True, capture=False, env=None):
    """Run a subprocess; raise on non-zero unless check=False."""
    res = subprocess.run(
        cmd, cwd=cwd, env=env,
        capture_output=capture, text=True,
    )
    if check and res.returncode != 0:
        out = (res.stdout or "") + (res.stderr or "")
        raise RuntimeError(f"command failed (rc={res.returncode}): {' '.join(cmd)}\n{out}")
    return res


def git(*args, **kwargs):
    return run(["git", *args], **kwargs)


def current_branch() -> str:
    return git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()


def working_tree_dirty() -> bool:
    out = git("status", "--porcelain", capture=True).stdout
    return bool(out.strip())


def conflicted_files() -> list[str]:
    out = git("diff", "--name-only", "--diff-filter=U", capture=True).stdout
    return [line for line in out.splitlines() if line]


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
        with open(prompt_file, "r") as pf:
            res = subprocess.run(cmd, stdin=pf, cwd=work_dir, text=True)
    finally:
        os.unlink(prompt_file)

    if res.returncode != 0:
        print(f"[sync] codex exec returned rc={res.returncode}", file=sys.stderr)
        return False

    # Verify resolution: no remaining conflicts and no MERGE_HEAD (commit was made).
    if conflicted_files():
        print(f"[sync] codex left unresolved conflicts: {conflicted_files()}", file=sys.stderr)
        return False
    merge_head = (REPO_ROOT / ".git" / "MERGE_HEAD").exists()
    if merge_head:
        print("[sync] codex resolved conflicts but did not commit (MERGE_HEAD still present)", file=sys.stderr)
        # Try to commit ourselves with a default message.
        git("commit", "--no-edit")
    return True


def merge_with_codex_fallback(target: str, label: str) -> bool:
    """Merge `target` into HEAD. On conflict, invoke codex once. Returns True on success."""
    print(f"[sync] {label}: merging {target}...")
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
        git("merge", "--abort", check=False)
        return False

    print(f"[sync] {label}: codex resolved conflicts and committed")
    return True


def push_branch(branch: str, *, set_upstream: bool = False) -> int:
    """Push `branch` to origin. Returns rc."""
    env = os.environ.copy()
    env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
    cmd = ["git", "push"]
    if set_upstream:
        cmd.extend(["--set-upstream", "origin", branch])
    else:
        cmd.extend(["origin", branch])
    res = subprocess.run(cmd, cwd=REPO_ROOT, env=env)
    return res.returncode


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
    git("checkout", "-b", branch, f"origin/{branch}")
    return True


def sync_one_direction(target: str, source: str, *, no_push: bool) -> bool:
    """Checkout `target`, merge `source` into it, push origin/<target>.
    Returns True on success."""
    if not ensure_local_tracks_origin(target):
        return False
    label = f"{target} <- {source}"
    if not merge_with_codex_fallback(source, label=label):
        return False
    if no_push:
        return True
    rc = push_branch(target)
    if rc != 0:
        print(f"[sync] push origin {target} failed (rc={rc})", file=sys.stderr)
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-push", action="store_true",
                        help="Skip the two pushes to origin (still does the merges locally)")
    args = parser.parse_args()

    original = current_branch()

    # Always fetch every ref from origin so both branches' remote state is
    # current before we attempt local merges.
    git("fetch", "origin", "--prune")

    # Working-tree dirty: stash with -u so untracked files come along.
    stashed = False
    if working_tree_dirty():
        print("[sync] working tree dirty; stashing with -u")
        git("stash", "push", "-u", "-m", f"sync_with_auto_dev autostash {os.getpid()}")
        stashed = True

    success = True
    try:
        # Step 0: auto-dev <- origin/dev
        # Pull external user / supervisor commits from `dev` (the main
        # upstream branch) into the stable mirror. On conflict, codex
        # resolves inside auto-dev (no need to involve codex-auto-dev
        # yet — the pipeline branch picks up the merged content via the
        # subsequent steps). If origin/dev doesn't exist (e.g. fresh
        # repo), this step is a no-op.
        if has_remote_branch(UPSTREAM_BRANCH):
            if not sync_one_direction(MIRROR_BRANCH, f"origin/{UPSTREAM_BRANCH}",
                                      no_push=args.no_push):
                success = False
                return
        else:
            print(f"[sync] origin/{UPSTREAM_BRANCH} missing; skipping dev → auto-dev step")

        # Step 1: codex-auto-dev <- auto-dev
        # Pulls auto-dev (now containing dev's content + any hand-edits)
        # into the pipeline integration branch so codex workers see them
        # on next round dispatch.
        if not sync_one_direction(SOURCE_BRANCH, f"origin/{MIRROR_BRANCH}",
                                  no_push=args.no_push):
            success = False
            return

        # Step 2: auto-dev <- codex-auto-dev
        # Mirrors the codex pipeline output back to the stable branch.
        # After this completes both branches point at the same commit
        # (or differ only by the merge commit direction).
        if not sync_one_direction(MIRROR_BRANCH, SOURCE_BRANCH,
                                  no_push=args.no_push):
            success = False
            return
    finally:
        # Always switch back to the branch the user started on.
        if original != current_branch():
            print(f"[sync] switching back to {original}")
            git("checkout", original, check=False)
        if stashed:
            print("[sync] restoring stash")
            git("stash", "pop", check=False)

    if success:
        print(f"[sync] done: {SOURCE_BRANCH} <-> {MIRROR_BRANCH} converged "
              f"(both pushed)" if not args.no_push else "(no-push)")
    else:
        sys.exit(2)


if __name__ == "__main__":
    main()

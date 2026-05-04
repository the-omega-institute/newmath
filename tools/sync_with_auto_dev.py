#!/usr/bin/env python3
"""Bidirectional sync between current local branch and `codex-auto-dev`.

Flow:
  1. fetch origin
  2. merge origin/codex-auto-dev into current branch (pull-direction)
  3. switch to codex-auto-dev (ff-pull from origin), merge current branch in
     (push-direction), push origin codex-auto-dev
  4. switch back to original branch

Both merges use `git merge --no-ff --no-edit` (no rebase). On conflict, codex
is invoked inside the working tree with a generic resolve prompt; codex is
expected to resolve conflicts, `git add`, and `git commit --no-edit` to
finalize the merge. If codex cannot resolve, the merge is aborted and the
script exits non-zero.

Working-tree dirty state is stashed (`git stash -u`) and restored after the
sync completes, including across the branch switch.
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
INTEGRATION_BRANCH = "codex-auto-dev"
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-push", action="store_true",
                        help="Skip pushing codex-auto-dev to origin")
    parser.add_argument("--push-current", action="store_true",
                        help="Also push the current branch back to its upstream after sync")
    args = parser.parse_args()

    original = current_branch()
    if original == INTEGRATION_BRANCH:
        print(f"[sync] already on {INTEGRATION_BRANCH}; doing simple ff-pull")
        git("fetch", "origin", INTEGRATION_BRANCH)
        git("merge", "--ff-only", f"origin/{INTEGRATION_BRANCH}")
        if not args.no_push:
            env = os.environ.copy()
            env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
            res = subprocess.run(["git", "push", "origin", INTEGRATION_BRANCH],
                                 cwd=REPO_ROOT, env=env)
            if res.returncode != 0:
                sys.exit(res.returncode)
        return

    # Working-tree dirty: stash with -u so untracked files come along.
    stashed = False
    if working_tree_dirty():
        print("[sync] working tree dirty; stashing with -u")
        git("stash", "push", "-u", "-m", f"sync_with_auto_dev autostash {os.getpid()}")
        stashed = True

    try:
        # Step 1: fetch.
        git("fetch", "origin", INTEGRATION_BRANCH)

        # Step 2: merge integration branch into current.
        if not merge_with_codex_fallback(f"origin/{INTEGRATION_BRANCH}",
                                         label=f"pull-direction ({original} <- {INTEGRATION_BRANCH})"):
            sys.exit(2)

        # Step 3: switch to integration branch and ff-pull.
        print(f"[sync] switching to {INTEGRATION_BRANCH}")
        git("checkout", INTEGRATION_BRANCH)
        try:
            git("merge", "--ff-only", f"origin/{INTEGRATION_BRANCH}")
        except RuntimeError as e:
            print(f"[sync] {INTEGRATION_BRANCH} ff-pull failed (likely diverged from origin): {e}",
                  file=sys.stderr)
            git("checkout", original, check=False)
            sys.exit(3)

        # Step 4: merge current branch back in.
        if not merge_with_codex_fallback(original,
                                         label=f"push-direction ({INTEGRATION_BRANCH} <- {original})"):
            git("checkout", original, check=False)
            sys.exit(4)

        # Step 5: push integration branch.
        if not args.no_push:
            env = os.environ.copy()
            env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
            res = subprocess.run(["git", "push", "origin", INTEGRATION_BRANCH],
                                 cwd=REPO_ROOT, env=env)
            if res.returncode != 0:
                print(f"[sync] push origin {INTEGRATION_BRANCH} failed (rc={res.returncode})",
                      file=sys.stderr)
                git("checkout", original, check=False)
                sys.exit(res.returncode)

        # Step 6: switch back.
        print(f"[sync] switching back to {original}")
        git("checkout", original)

        # Step 7: optionally push current branch.
        if args.push_current:
            env = os.environ.copy()
            env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
            res = subprocess.run(["git", "push", "origin", original],
                                 cwd=REPO_ROOT, env=env)
            if res.returncode != 0:
                sys.exit(res.returncode)
    finally:
        if stashed:
            print("[sync] restoring stash")
            git("stash", "pop", check=False)

    print(f"[sync] done: {original} <-> {INTEGRATION_BRANCH} synchronized")


if __name__ == "__main__":
    main()

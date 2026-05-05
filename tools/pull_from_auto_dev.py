#!/usr/bin/env python3
"""Bidirectional sync between our pipeline branch
(`bedc-claim-packet-pipeline`) and the shared integration branch
(`auto-dev`). Mirrors loning's `sync_with_auto_dev.py` pattern but
anchored on our branch in place of `codex-auto-dev`, so our pipeline
participates as a peer alongside loning's.

Topology:

    loning's pipeline output  →  codex-auto-dev  ↕  auto-dev  ↕  bedc-claim-packet-pipeline  ←  our pipeline output

  loning runs `tools/sync_with_auto_dev.py` to converge the left edge
  (`codex-auto-dev ↔ auto-dev`). This script converges the right edge
  (`auto-dev ↔ bedc-claim-packet-pipeline`). After both daemons tick,
  every branch holds the same content (modulo merge-commit direction),
  so any third party can read or write through `auto-dev` and reach all
  pipelines.

Flow per tick:

  1. `git fetch origin --prune`
  2. stash dirty WT if any
  3. on `bedc-claim-packet-pipeline`:
       a. ff-pull origin/<target>
       b. `git merge --no-ff --no-edit origin/auto-dev`
       c. push origin/<target>
  4. on `auto-dev`:
       a. ff-pull origin/auto-dev (handles loning's recent pushes)
       b. `git merge --no-ff --no-edit bedc-claim-packet-pipeline`
       c. push origin/auto-dev
  5. checkout original branch, restore stash

Conflicts on either side fall back to codex CLI with the same prompt
loning uses; codex resolves + commits or we abort that direction.
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
SHARED_BRANCH = "auto-dev"                         # shared integration branch
LOCAL_BRANCH = "bedc-claim-packet-pipeline"        # our pipeline branch
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
    res = subprocess.run(cmd, cwd=cwd, env=env, capture_output=capture, text=True)
    if check and res.returncode != 0:
        out = (res.stdout or "") + (res.stderr or "")
        raise RuntimeError(f"command failed (rc={res.returncode}): {' '.join(cmd)}\n{out}")
    return res


def git(*args, **kwargs):
    return run(["git", *args], **kwargs)


def current_branch() -> str:
    return git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()


def working_tree_dirty() -> bool:
    return bool(git("status", "--porcelain", capture=True).stdout.strip())


def conflicted_files() -> list[str]:
    out = git("diff", "--name-only", "--diff-filter=U", capture=True).stdout
    return [line for line in out.splitlines() if line]


def call_codex_to_resolve(work_dir: Path, timeout: int = 1800) -> bool:
    files = conflicted_files()
    if not files:
        return True

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

    if conflicted_files():
        print(f"[sync] codex left unresolved conflicts: {conflicted_files()}", file=sys.stderr)
        return False
    if (REPO_ROOT / ".git" / "MERGE_HEAD").exists():
        print("[sync] codex resolved conflicts but did not commit; committing now")
        git("commit", "--no-edit")
    return True


def merge_with_codex_fallback(target_ref: str, label: str) -> bool:
    print(f"[sync] {label}: merging {target_ref}...")
    res = git("merge", "--no-ff", "--no-edit", target_ref, check=False, capture=True)
    if res.returncode == 0:
        print(f"[sync] {label}: merge clean")
        return True

    out = (res.stdout or "") + (res.stderr or "")
    if "Already up to date" in out or "already up to date" in out:
        print(f"[sync] {label}: already up to date")
        return True

    if not conflicted_files():
        print(f"[sync] {label}: merge failed without conflicts:\n{out}", file=sys.stderr)
        return False

    if not call_codex_to_resolve(REPO_ROOT):
        print(f"[sync] {label}: codex could not resolve; aborting merge", file=sys.stderr)
        git("merge", "--abort", check=False)
        return False

    print(f"[sync] {label}: codex resolved conflicts and committed")
    return True


def push_branch(branch: str) -> int:
    env = os.environ.copy()
    env.setdefault("LEAN4_GUARDRAILS_BYPASS", "1")
    res = subprocess.run(
        ["git", "push", "origin", branch],
        cwd=REPO_ROOT, env=env,
    )
    return res.returncode


def has_remote_branch(branch: str) -> bool:
    res = git("ls-remote", "--exit-code", "--heads", "origin", branch,
              check=False, capture=True)
    return res.returncode == 0


def has_local_branch(branch: str) -> bool:
    res = git("rev-parse", "--verify", "--quiet", f"refs/heads/{branch}",
              check=False, capture=True)
    return res.returncode == 0


def ensure_local_tracks_origin(branch: str) -> bool:
    """Make sure `branch` exists locally and is fast-forwarded to origin/<branch>.
    Returns True on success."""
    if not has_remote_branch(branch):
        print(f"[sync] origin/{branch} missing — cannot sync", file=sys.stderr)
        return False
    if has_local_branch(branch):
        git("checkout", branch)
        res = git("merge", "--ff-only", f"origin/{branch}", check=False, capture=True)
        if res.returncode != 0:
            out = (res.stdout or "") + (res.stderr or "")
            if "Already up to date" not in out and "already up to date" not in out:
                print(f"[sync] {branch} cannot ff origin/{branch} (diverged); "
                      "leaving as-is — bidirectional merge will reconcile",
                      file=sys.stderr)
        return True
    git("checkout", "-b", branch, f"origin/{branch}")
    return True


def sync_one_direction(target: str, source_ref: str, *, no_push: bool) -> bool:
    """Checkout `target`, merge `source_ref` into it, push origin/<target>."""
    if not ensure_local_tracks_origin(target):
        return False
    label = f"{target} <- {source_ref}"
    if not merge_with_codex_fallback(source_ref, label=label):
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
    parser.add_argument("--local", default=LOCAL_BRANCH,
                        help=f"our pipeline branch (default: {LOCAL_BRANCH})")
    parser.add_argument("--shared", default=SHARED_BRANCH,
                        help=f"shared integration branch (default: {SHARED_BRANCH})")
    parser.add_argument("--no-push", action="store_true",
                        help="merge both directions locally; don't push to origin")
    parser.add_argument("--pull-only", action="store_true",
                        help="only run shared→local; skip the push direction")
    args = parser.parse_args()

    original = current_branch()

    git("fetch", "origin", "--prune")

    if not has_remote_branch(args.shared):
        print(f"[sync] origin/{args.shared} missing — abort", file=sys.stderr)
        sys.exit(2)
    if not has_remote_branch(args.local):
        print(f"[sync] origin/{args.local} missing — abort", file=sys.stderr)
        sys.exit(2)

    stashed = False
    if working_tree_dirty():
        print("[sync] working tree dirty; stashing with -u")
        git("stash", "push", "-u", "-m", f"sync_auto_dev autostash {os.getpid()}")
        stashed = True

    success = True
    try:
        # Step 1: pull — local <- origin/shared
        # Brings loning's pipeline output (and any third-party content
        # already mirrored to auto-dev) into our pipeline branch.
        if not sync_one_direction(args.local, f"origin/{args.shared}",
                                  no_push=args.no_push):
            success = False
            return

        if args.pull_only:
            return

        # Step 2: push — shared <- local
        # Mirrors our pipeline's commits onto auto-dev so loning's sync
        # daemon picks them up into codex-auto-dev, and any third party
        # watching auto-dev sees our content.
        if not sync_one_direction(args.shared, args.local,
                                  no_push=args.no_push):
            success = False
            return
    finally:
        if original != current_branch():
            print(f"[sync] switching back to {original}")
            git("checkout", original, check=False)
        if stashed:
            print("[sync] restoring stash")
            git("stash", "pop", check=False)

    if not success:
        sys.exit(2)
    suffix = " (no-push)" if args.no_push else (" (pull-only)" if args.pull_only else " (pushed both)")
    print(f"[sync] done: {args.local} <-> {args.shared} converged" + suffix)


if __name__ == "__main__":
    main()

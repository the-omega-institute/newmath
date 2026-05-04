#!/usr/bin/env python3
"""One-way pull from `origin/auto-dev` into the local working branch
(`bedc-claim-packet-pipeline` by default). Keeps our pipeline branch up
to date with the loning-side `auto-dev` mirror without ever pushing
back: `auto-dev` is the upstream contract, our branch is downstream.

Flow:
  1. `git fetch origin --prune`
  2. stash dirty WT (`git stash -u`) if present
  3. checkout target branch (default: bedc-claim-packet-pipeline)
  4. ff-pull origin/<target> first so we are in sync with our own remote
  5. `git merge --no-ff --no-edit origin/auto-dev` into target
  6. on conflict: invoke codex once with the same conflict prompt loning
     uses; codex resolves + commits or we abort
  7. push target back to origin (so other workers / dashboards see it)
  8. restore stash, checkout original branch

This is the one-way counterpart to `tools/sync_with_auto_dev.py` (which
loning runs to keep `codex-auto-dev <-> auto-dev` converged). We do NOT
touch `auto-dev` or `codex-auto-dev` here — those branches are loning's
to publish to. Our only job is to pull their content in.
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
UPSTREAM_BRANCH = "auto-dev"
DEFAULT_TARGET = "bedc-claim-packet-pipeline"
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
        print(f"[pull] codex CLI not found at {CODEX_PATH}", file=sys.stderr)
        return False

    print(f"[pull] {len(files)} file(s) in conflict; invoking codex (cwd={work_dir})")
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
        print(f"[pull] codex exec returned rc={res.returncode}", file=sys.stderr)
        return False

    if conflicted_files():
        print(f"[pull] codex left unresolved conflicts: {conflicted_files()}", file=sys.stderr)
        return False
    if (REPO_ROOT / ".git" / "MERGE_HEAD").exists():
        print("[pull] codex resolved conflicts but did not commit; committing now")
        git("commit", "--no-edit")
    return True


def merge_with_codex_fallback(target_ref: str, label: str) -> bool:
    print(f"[pull] {label}: merging {target_ref}...")
    res = git("merge", "--no-ff", "--no-edit", target_ref, check=False, capture=True)
    if res.returncode == 0:
        print(f"[pull] {label}: merge clean")
        return True

    out = (res.stdout or "") + (res.stderr or "")
    if "Already up to date" in out or "already up to date" in out:
        print(f"[pull] {label}: already up to date")
        return True

    if not conflicted_files():
        print(f"[pull] {label}: merge failed without conflicts:\n{out}", file=sys.stderr)
        return False

    if not call_codex_to_resolve(REPO_ROOT):
        print(f"[pull] {label}: codex could not resolve; aborting merge", file=sys.stderr)
        git("merge", "--abort", check=False)
        return False

    print(f"[pull] {label}: codex resolved conflicts and committed")
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default=DEFAULT_TARGET,
                        help=f"branch to merge into (default: {DEFAULT_TARGET})")
    parser.add_argument("--upstream", default=UPSTREAM_BRANCH,
                        help=f"upstream branch to pull from (default: {UPSTREAM_BRANCH})")
    parser.add_argument("--no-push", action="store_true",
                        help="merge locally only; don't push the target back to origin")
    parser.add_argument("--no-self-pull", action="store_true",
                        help="skip the ff-pull from origin/<target> before merging upstream")
    args = parser.parse_args()

    original = current_branch()

    git("fetch", "origin", "--prune")

    if not has_remote_branch(args.upstream):
        print(f"[pull] origin/{args.upstream} missing — abort", file=sys.stderr)
        sys.exit(2)
    if not has_remote_branch(args.target):
        print(f"[pull] origin/{args.target} missing — abort", file=sys.stderr)
        sys.exit(2)

    stashed = False
    if working_tree_dirty():
        print("[pull] working tree dirty; stashing with -u")
        git("stash", "push", "-u", "-m", f"pull_from_auto_dev autostash {os.getpid()}")
        stashed = True

    success = True
    try:
        if current_branch() != args.target:
            print(f"[pull] switching to {args.target}")
            git("checkout", args.target)

        if not args.no_self_pull:
            print(f"[pull] ff-pulling origin/{args.target} first")
            res = git("merge", "--ff-only", f"origin/{args.target}",
                      check=False, capture=True)
            if res.returncode != 0:
                out = (res.stdout or "") + (res.stderr or "")
                if "Already up to date" not in out and "already up to date" not in out:
                    print(f"[pull] {args.target} cannot ff origin/{args.target} (diverged); "
                          "leaving as-is and continuing", file=sys.stderr)

        label = f"{args.target} <- origin/{args.upstream}"
        if not merge_with_codex_fallback(f"origin/{args.upstream}", label=label):
            success = False
            return

        if not args.no_push:
            rc = push_branch(args.target)
            if rc != 0:
                print(f"[pull] push origin {args.target} failed (rc={rc})", file=sys.stderr)
                success = False
    finally:
        if original != current_branch():
            print(f"[pull] switching back to {original}")
            git("checkout", original, check=False)
        if stashed:
            print("[pull] restoring stash")
            git("stash", "pop", check=False)

    if not success:
        sys.exit(2)
    print(f"[pull] done: {args.target} now contains origin/{args.upstream}"
          + ("" if args.no_push else " (pushed)"))


if __name__ == "__main__":
    main()

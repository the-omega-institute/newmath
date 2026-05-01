---
name: bedc-codex-auto-dev
description: Start and monitor the BEDC paper revision and Lean formalization Codex pipelines on the shared codex-auto-dev integration branch.
allowed-tools: Bash, Monitor
---

# BEDC shared Codex pipelines

Use this skill when the user asks to run both BEDC Codex pipelines together, to use `codex-auto-dev`, or to monitor paper and Lean automation on one shared branch.

## Branch

Always use:

```bash
--base-branch codex-auto-dev
```

Do not pass `--peer-branch` to the paper script in this mode. Both pipelines merge directly into the same integration branch.

## Preflight

Before starting anything, check whether matching processes are already running:

```bash
ps -axo pid,ppid,pgid,stat,etime,command | grep -E 'codex_revise.py|codex_formalize.py' | grep -v grep
```

Then check both pipeline statuses:

```bash
python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py --base-branch codex-auto-dev --status
python3 /Users/chronoai/newmath/lean4/scripts/codex_formalize.py --base-branch codex-auto-dev --status
```

If either pipeline is already running on `codex-auto-dev`, do not start a duplicate. Report what is already running and monitor it instead.

## Start and monitor

Use `Monitor`, not a separate background Bash launcher, so the command both starts and streams actionable events.

Paper command:

```bash
python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py --base-branch codex-auto-dev --resume && python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py --base-branch codex-auto-dev --parallel 5 --continuous --peer-sync-interval 0 2>&1 | grep -E --line-buffered 'SUCCESS|FAILED|ERROR|WARNING|Exception|Traceback|Push rejected|Rebase conflict|Merging|Merged|P[0-9]+'
```

Lean command:

```bash
python3 /Users/chronoai/newmath/lean4/scripts/codex_formalize.py --base-branch codex-auto-dev --parallel 5 --continuous --lake-parallel 1 2>&1 | grep -E --line-buffered 'SUCCESS|FAILED|ERROR|WARNING|Exception|Traceback|Push rejected|Rebase conflict|Merging|Merged|builder|PASS|FAIL|R[0-9]+'
```

Use `persistent: true` for both monitors. Describe them as:

- `BEDC paper pipeline on codex-auto-dev`
- `BEDC Lean pipeline on codex-auto-dev`

## Stop commands

For an orderly stop, run:

```bash
python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py --stop
python3 /Users/chronoai/newmath/lean4/scripts/codex_formalize.py --stop
```

Then confirm remaining processes with the preflight process check. If orphaned child process groups remain, terminate only the specific matching process groups after verifying their command lines.

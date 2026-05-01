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

## Monitoring duty: content quality and merge efficiency

While the pipelines run, keep watching two axes. When a signal appears, edit the prompts (instant — re-read on each round dispatch) or the pipeline scripts (requires stop + restart) and bump prompt versions so commit bodies record which prompt pair produced them.

### Content-quality signals

After every merged commit, sample `git show <sha>` and check for:

1. **Parameter-echo theorems.** Statements that introduce abstract parametric carriers $A,B$ and classifiers $\sim_A,\sim_B$ as universally quantified inputs and conclude with paired field-by-field $\Leftrightarrow$ chains. The proof is "transport hypothesis through the equivalence on each field." This is bookkeeping, not theory growth — `papers/bedc/scripts/prompts/phase_review.txt` (paper) and `lean4/scripts/prompts/phase_c.txt` (Lean discovery insertion) reject these.
2. **Same-file saturation.** Multiple consecutive commits touching the same `papers/bedc/parts/<theme>/<file>.tex` with `source-equivalence` / `under-source-equivalence` / `_with_fields` / `_alt` siblings. The paper review prompt counts the last 20 paper-side commits; ≥3 hits triggers an extra bar.
3. **Label collision.** Two `\label{thm:X}` with identical X anywhere under `papers/bedc/parts/`. Detect with `python3 lean4/scripts/bedc_ci.py audit` — duplicate labels are now printed on stdout with `<label> @ <file>:<line>, <file>:<line>`. Empty stdout for duplicates means the audit silent bug regressed.
4. **Marker mismatch.** A new `\leanchecked{X}` / `\leanstmt{X}` / `\leandef{X}` whose X cannot be resolved under `lean4/BEDC/`. Same audit reports these with `[bedc-ci] unresolved Lean markers:`.
5. **Empty / register-only round.** A commit whose Lean diff is zero insertions (Lean rounds) or whose paper diff is whitespace / pure-marker (paper rounds). Each side has a HARD GATE in its phase prompt; if such a commit lands, the gate is leaking.

When a signal repeats across ≥2 commits, treat it as systematic and edit the relevant prompt or script the same session.

### Merge-efficiency signals

The merge path is high-risk because two pipelines share `codex-auto-dev`:

- **`ff update of codex-auto-dev failed`**: the main repo's working tree is dirty (often: a code edit done concurrently with an in-flight merge). Resolve by committing or stashing the local changes, then resume.
- **`Pre-merge hard gate failed: ... bedc_ci.py audit`** (Lean): means rebase introduced a duplicate label or marker mismatch from a concurrent paper round. The audit-stdout will name the offending label — the script auto-routes to `_codex_resolve_post_rebase_audit` to drop this round's colliding additions.
- **`Drift audit OK` followed by ff fail in paper merge**: paper's drift audit runs in the worktree pre-rebase, so it cannot see sibling-induced collisions. The newly added post-rebase audit + codex resolver in `codex_revise.py::merge_worktree_to_base` catches this.
- **`Diverging branches can't be fast-forwarded`**: rebase resolution by codex left the round branch off the BASE_BRANCH lineage. Round will FAIL. Investigate the codex resolution log.
- **`3 consecutive failures — sleeping 180s`**: cooldown trigger. Look at the failing rounds' Phase B output files (`lean4/scripts/logs/codex/R<N>_phaseB_*.out.txt`); zero-byte means codex was killed externally (not a prompt issue), non-zero means inspect the gate that rejected it.

### Editing prompts

Prompt files are re-read on each round dispatch — edits are live for the next round to start.

- Paper: `papers/bedc/scripts/prompts/phase_review.txt`, `phase_revise.txt` — bump the `## Prompts version` line in BOTH files when either changes (e.g. v1.6 → v1.7). The version is mirrored into commit bodies as `prompts: vN.M`.
- Lean: `lean4/scripts/prompts/phase_b.txt`, `phase_c.txt` — same convention (e.g. v3.0 → v3.1).

### Editing scripts

Script edits do NOT take effect for in-flight rounds (the Python process loaded them at startup). After editing a script:

1. Either `--stop` and let drain finish, or accept that current rounds use the old logic.
2. Commit the script change to `codex-auto-dev` BEFORE restart, otherwise `ff update of codex-auto-dev failed` will block in-flight merges that touch the work tree.
3. Restart with the same Monitor commands as above.

Common script files:
- `lean4/scripts/bedc_ci.py` — `cmd_audit` prints duplicate labels + unresolved markers + forbidden constructs; failures contribute to non-zero exit code.
- `papers/bedc/scripts/codex_revise.py` — `merge_worktree_to_base` runs post-rebase drift audit; `_codex_resolve_post_rebase_audit` drops a round's colliding paper additions.
- `lean4/scripts/codex_formalize.py` — `run_pre_merge_hard_gates` returns `(ok, gate_name, tail)`; `_codex_resolve_post_rebase_audit` is the symmetric Lean-side recovery for paper-side stale labels.

### Fast triage commands

Quality:
```bash
git -C /Users/chronoai/newmath log --oneline codex-auto-dev | head -20
python3 /Users/chronoai/newmath/lean4/scripts/bedc_ci.py audit
git -C /Users/chronoai/newmath log --stat -10 -- papers/bedc/parts/  # spot saturated files
```

Merge:
```bash
ps -axo pid,etime,command | grep -E 'codex_revise|codex_formalize' | grep -v grep
git -C /Users/chronoai/newmath worktree list
git -C /Users/chronoai/newmath status --short  # MUST be empty while rounds are merging
```

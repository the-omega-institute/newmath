---
name: bedc-codex-auto-dev
description: Start and monitor the BEDC paper revision and Lean formalization Codex pipelines on the shared codex-auto-dev integration branch.
allowed-tools: Bash, Monitor
---

# BEDC shared Codex pipelines

Use this skill when the user asks to run both BEDC Codex pipelines together, to use `codex-auto-dev`, or to monitor paper and Lean automation on one shared branch.

## Path convention

All shell commands in this skill use `$REPO` as the repo root. Set it once per shell session before running any commands:

```bash
export REPO="$(git rev-parse --show-toplevel)"
```

Every subsequent `python3 $REPO/...` / `tail $REPO/...` / `mkdir $REPO/...` then resolves correctly regardless of the user's current working directory or machine layout.

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
python3 $REPO/papers/bedc/scripts/codex_revise.py --base-branch codex-auto-dev --status
python3 $REPO/lean4/scripts/codex_formalize.py --base-branch codex-auto-dev --status
```

If either pipeline is already running on `codex-auto-dev`, do not start a duplicate. Report what is already running and monitor it instead.

## Start (background, detached)

**Always launch the orchestrators as fully-detached background processes — never inside a `Monitor` and never piped through anything that the harness owns.** The orchestrator must outlive any Claude Code session, Monitor swap, or filter change. Use `nohup … &` plus `disown` so the process re-parents to PID 1 and survives shell exit.

Use the `Bash` tool. Do **not** also pass `run_in_background: true` — `nohup … &` + `disown` already detaches; double-backgrounding only confuses cleanup.

Paper:

```bash
mkdir -p $REPO/papers/bedc/scripts/logs && \
nohup bash -c '
  python3 $REPO/papers/bedc/scripts/codex_revise.py \
    --base-branch codex-auto-dev --resume && \
  python3 $REPO/papers/bedc/scripts/codex_revise.py \
    --base-branch codex-auto-dev --continuous --peer-sync-interval 0
' >> $REPO/papers/bedc/scripts/logs/orchestrator.log 2>&1 &
disown
```

Lean:

```bash
mkdir -p $REPO/lean4/scripts/logs && \
nohup python3 $REPO/lean4/scripts/codex_formalize.py \
  --base-branch codex-auto-dev --continuous \
  --phase-b-timeout 3600 --phase-c-timeout 4500 \
  >> $REPO/lean4/scripts/logs/orchestrator.log 2>&1 &
disown
```

Branch sync daemon (third default-launched component):

```bash
mkdir -p $REPO/scripts/logs && \
nohup bash -c '
  while true; do
    python3 $REPO/tools/sync_with_auto_dev.py 2>&1 \
      | sed "s/^/[sync] /"
    sleep 600
  done
' >> $REPO/scripts/logs/sync_daemon.log 2>&1 &
disown
```

The sync daemon runs `tools/sync_with_auto_dev.py` every 10 min (600s). Purpose: the two orchestrators only sync inside their own worktrees — they never push commits made directly on the main checkout (e.g. SKILL.md / prompt edits / hub splits done in this session). Without the daemon, those commits sit local until you remember to push. With the daemon, they get bidirectionally merged + pushed within 10 min. On conflict, the script invokes codex inside the worktree to resolve. When the main checkout is already on `codex-auto-dev` and clean (the typical case), the script degrades to a `git fetch + ff-only pull + push` — cheap, no merge commit churn.

Concurrency autotune daemon (fourth default-launched component):

```bash
mkdir -p $REPO/scripts/logs && \
nohup bash -c '
  while true; do
    ts=$(date "+%Y-%m-%d %H:%M:%S")
    echo "[autotune] $ts tick"
    python3 $REPO/tools/auto_tune_concurrency.py 2>&1
    sleep 300
  done
' >> $REPO/scripts/logs/autotune_daemon.log 2>&1 &
disown
```

`tools/auto_tune_concurrency.py` reads `critical_path.py` JSON output (top size, root_unblocks count) and resizes `.pipeline_parallel.json`'s `paper` / `lean` / `lean_lake` keys to match available work supply. Formula: `lean = clamp(top_size, 3, 15)` (no buffer — observed in 2026-05-06 session that `top_size + 3` caused chapter dogpile when supply was tight; multiple workers picked overlapping `BHist*_classifier_transport` neighbors and produced dup-decl lake-build failures); `paper = clamp(root_unblocks + 4, 3, 8)`; `lean_lake = clamp(lean // 5, 1, 3)`. Hot-reload — every round dispatch reads the JSON. Without autotune, static concurrency settings drift out of phase with the changing dep tree as paper rounds unlock chapters and oversubscribe lean workers, burning Phase B / lake build budget on collisions.

BASE auto-heal daemon (fifth default-launched component):

```bash
mkdir -p $REPO/scripts/logs && \
nohup python3 $REPO/tools/auto_heal_base.py >> $REPO/scripts/logs/auto_heal.log 2>&1 &
disown
```

`tools/auto_heal_base.py` runs every 15 min (`AUTO_HEAL_INTERVAL_SECONDS` env override, default 900s). Cycle: fetch + ff codex-auto-dev → run `bedc_ci.py audit` → if dup paper labels detected on BASE, invoke codex with `HEAL_DUP_LABELS_PROMPT` to delete the redundant copy (canonical-site rules: hub vs sibling, semantic stem matching). Codex commits the cleanup directly on main checkout, daemon pushes to origin. Without this, a single duplicate-label commit on BASE stalls every subsequent round in audit-fail / SHALLOW-GROWTH cooldown loops indefinitely (observed 2026-05-06: 9 cooldowns × 180s + 36 SHALLOW lints over 30 min before manual surgery resolved). Skips when the working tree is dirty or branch isn't codex-auto-dev — never fights a human edit.

### Verify restart success (two-step, never skip)

After launching, run **two sequential one-shot checks** before declaring the restart healthy. Skipping either check has bitten the operator.

**Step 1 — process check:**

```bash
ps -axo pid,ppid,pgid,etime,command | grep -E 'codex_revise.py|codex_formalize.py|sync_with_auto_dev.py|auto_tune_concurrency|auto_heal_base' | grep -v grep
```

All five processes (paper orchestrator, lean orchestrator, sync daemon, autotune daemon, auto-heal daemon) must appear with `PPID=1` (init). If `PPID` is your shell's PID, `disown` didn't take and a session exit will SIGHUP the orchestrator. If any one is missing entirely, the script crashed before it ever wrote a log line — go read the relevant log tail to see the import / argparse error.

**Step 2 — progress check:**

```bash
sleep 8 && tail -3 $REPO/lean4/scripts/logs/orchestrator.log; echo '---paper---'; tail -3 $REPO/papers/bedc/scripts/logs/orchestrator.log; echo '---sync---'; tail -3 $REPO/scripts/logs/sync_daemon.log
```

Each log should show recent timestamps (within the last ~10s for orchestrators; within the last ~600s for sync) and substantive lines: `Phase B: Target selection...` / `Phase REVIEW: theory audit...` / `Calling codex exec ...` for the orchestrators; `[sync] [sync] done: ... synchronized` or `[sync] already on codex-auto-dev` for the daemon. **Use one-shot `tail -N`, not persistent `tail -F`.** A persistent `tail -F` blocks forever waiting for output, so if startup actually crashed silently between Step 1 and Step 2 (e.g. PID-lock not released, port in use, env var missing), the persistent monitor never fires a notification — you'd think you were watching it and it'd just be hanging. One-shot tails return immediately and let you verify by inspection.

Only after BOTH steps pass — processes alive with PPID=1 AND logs advancing past startup — should you optionally arm a persistent `tail -F` for ongoing observation (see "Monitor" section below). The persistent monitor is for steady-state observation, never for verifying that startup succeeded.

`--phase-b-timeout` and `--phase-c-timeout` defaults (2700 / 3600) are too tight under high parallelism: bump to 3600 / 4500. These are CLI-only — restart required to change.

## Tuning concurrency live (no restart)

Concurrency is read from `<repo>/.pipeline_parallel.json` on every round dispatch — edit the file and the next dispatched round picks up the new value. **CLI `--parallel` and `--lake-parallel` flags are deprecated; the JSON file is the only source of truth at runtime.**

```json
{"paper": 8, "lean": 12, "lean_lake": 3}
```

| Key | Effect | Sane range |
|---|---|---|
| `paper` | Concurrent paper rounds (Phase REVIEW / REVISE / VERIFY / merge overlap; codex-exec children = ~paper) | 5–10 |
| `lean` | Concurrent lean rounds | 8–14 |
| `lean_lake` | Concurrent `lake build` invocations gated by the lake mutex; was hard-coded 1 historically | 1–3 (3 fits in 16 GB if memory pressure is moderate) |

Memory floor is the binding constraint, not CPU — each codex-exec child is ~50–100 MB; each `lake build` is ~1–1.5 GB. With `lean_lake: 3` and 16 GB RAM, leaving `paper + lean ≤ ~20` keeps `vm_stat` "free" above 0.5 GB. The orchestrator's memory_guard kicks in only when `swap > 16 GB AND avail < 1.5 GB`, so the JSON file is your knob, not the guard.

**Autotune daemon overrides static settings.** Once `tools/auto_tune_concurrency.py` is launched (5th default daemon, see Start section), it re-writes `paper` / `lean` / `lean_lake` every 300s based on critical_path supply. Manual edits get overwritten on the next tick. To override autotune, either kill the autotune daemon first or change its constants (`LEAN_BUFFER` / `PAPER_BUFFER` / clamp ranges) and let it pick up the new formula. The `lean = top_size` (no buffer) formula is empirical; raising `LEAN_BUFFER` reintroduces chapter dogpile at low supply. Lowering autotune `*_MAX` constants is the right way to cap concurrency under sustained memory pressure.

## Monitor (read-only, never owns the orchestrator)

Monitors `tail -F` the log files the detached orchestrators write to. They are pure observers — killing, swapping, or re-launching a Monitor never touches the orchestrator process.

### Token-saving monitor mode (default)

Operate in **token-saving** mode by default. Each Monitor event resolves to **one short Chinese sentence** (≤25 字), no diagnostics commands, no log quotes, no tables. The recovery consumer + Phase D lints + closure machinery handle issues automatically, so an event arriving in your transcript is mostly informational — your job is to acknowledge that you saw it and that automation took over, not to investigate.

Concrete rules for token-saving replies:

1. **Recurring patterns (`Round FAILED` + ticket queued, `Merge failed —` + recovery picked up, `SHALLOW GROWTH` + ticket queued)**: one sentence — `R2364 SHALLOW GROWTH 抓住 dup → recovery 已接管` style. Don't quote the offending names, don't speculate. Stop there.
2. **First occurrence of a new pattern (not seen this session)**: still one sentence, but flag it — `首次见到 X，观察 1-2 例后再决定要不要加 gate`. Then drop it.
3. **`[recovery] RECOVERED` / `[recovery] unrecoverable`**: one sentence. RECOVERED is positive; unrecoverable means the worktree was marked dead and the operator may need to look at the dead/ folder later — but not now.
4. **`closure_mark` / `deps_ready_relaxed`**: ack as positive signal in one sentence.
5. **`[sync] codex could not resolve` / `push origin … failed`**: this is real — escalate with one sentence describing what to do (`sync daemon 调 codex 解冲突失败，等下一轮 600s 后重试 / 或手动 sync_with_auto_dev.py`).
6. **3 events of the same kind in one tick**: one combined sentence covering all three (`R2364/R2365/R2367 都 dup-ticket→recovery，pattern 一致`). Don't reply per-event.
7. **No actionable events in a tick**: zero output is fine.
8. **Verbose mode override**: only switch to long-form when (a) the user asks `详细分析` / `深入看看` / `report` / `调查 ...`, (b) a self-check `/loop` tick fires, or (c) the same novel pattern repeats ≥3 times in 30 min — then briefly pull stats and propose a prompt edit.

Token-saving replies do NOT spawn shell commands unless you actually need data to decide whether action is warranted (rule 5 / rule 8). For the default ack-only path, reply with text alone.

Default to a single **active error watch** that tails BOTH log files at once and emits only actionable signals. SUCCESS / Phase transitions / audit-OK / PDF-OK / routine ff-race events are silenced; the recovery consumer + closure machinery handle most issues automatically, so events that DO arrive are ones you can act on (edit a prompt, edit `critical_path.py`, edit `.pipeline_parallel.json`, queue a manual recovery ticket).

```bash
tail -F $REPO/papers/bedc/scripts/logs/orchestrator.log \
       $REPO/lean4/scripts/logs/orchestrator.log \
       $REPO/scripts/logs/sync_daemon.log \
       $REPO/scripts/logs/auto_heal.log \
  | grep -E --line-buffered \
      'Round FAILED|Merge failed —|3 consecutive failures|Codex did not complete|Codex could not resolve|\[recovery\]\s+(queued|picking|RECOVERED|unrecoverable|codex crashed|stopped)|Pre-merge hard gate failed|STALE MARKER|SHALLOW GROWTH|Phase B failed:|Phase C failed:|Phase D failed:|Traceback|^[^:]+:\s+\bException:|builder.*FAIL|deps_ready_relaxed.*[Tt]rue|closure_mark|memory_guard.*PAUSE|Session complete:|draining [0-9]+ in-flight workers|Pipeline PID token is not current|\[sync\] .*(codex could not resolve|push origin codex-auto-dev failed|merge failed without conflicts)|\[heal\] .*(detected|committed|push failed)'
```

Use `persistent: true`. Describe as `BEDC active error watch`.

What each pattern means and the cheapest fix:

| Pattern | Meaning | Fix without restart |
|---|---|---|
| `Round FAILED` | Worker FAILed; if commits exist, recovery queue auto-takes |
| `Merge failed —` | merge_worktree_to_base exhausted retries; recovery queue auto-takes |
| `3 consecutive failures` | Cooldown; usually paper-led horizon thresholds shifting — wait or lower `deps_ready_threshold` in `.pipeline_parallel.json` |
| `Codex did not complete` / `could not resolve` | Codex resolver gave up; recovery queue picks it up next |
| `[recovery] queued/picking/...` | Recovery consumer activity; positive signal that catch-all is working |
| `Pre-merge hard gate failed: <gate>` | Specific gate failed (lake build / audit / axiom-purity / phase_d_lint) — recovery consumer attempts codex fix |
| `STALE MARKER` | Paper marker references missing Lean target — codex prompt issue or paper-side cleanup needed |
| `SHALLOW GROWTH` | Phase D lint detected duplicate / parameter-echo / mechanical-arity — prompt rule issue |
| `Phase B failed: no targets extracted` | critical_path empty top OR codex couldn't pick — check `deps_ready_relaxed` or lower threshold |
| `deps_ready_relaxed: True` | critical_path auto-relaxed `deps_ready_threshold` because strict yielded empty — informational |
| `closure_mark` | Paper review proposed a `\closureat` for a chapter — positive signal that closure machinery is working |
| `memory_guard.*PAUSE` | Lean orchestrator paused workers due to memory pressure — drop `lean_lake` or `lean` in `.pipeline_parallel.json` |
| `Session complete: N succeeded, M failed` / `draining N in-flight workers` / `Pipeline PID token is not current` | **Orchestrator exited or got swapped out.** Under `--continuous`, neither side should ever print these — they mean the loop terminated and no one will dispatch new rounds. Run the liveness check below and, if a daemon is missing, restart it (see "Start" / "Stop" sections). This is the single most disruptive silent failure mode: paper-side keeps crunching closure_mark while lean side hasn't moved in hours, and `closed_horizons` totals can still drift up from paper alone, masking the outage. |

If you need verbose per-phase visibility for a debugging session, swap the filter to `'SUCCESS|FAILED|ERROR|WARNING|Exception|Traceback|Push rejected|Merge conflict|Merging|Merged|[PR][0-9]+'`. Don't leave the verbose filter on a long-running monitor — it produces 20+ events/min during steady state and burns transcript tokens.

### Liveness health check (run at every status query)

Whenever the user asks `状态如何` / `现在如何` / `进展` / `report`, **before** computing closure deltas, run a one-shot daemon liveness probe. Three daemons must each appear with `PPID=1`:

```bash
ps -axo pid,ppid,etime,command \
  | grep -E 'codex_revise.py|codex_formalize.py|sync_with_auto_dev.py' \
  | grep -v grep
```

Expected:

- one `codex_revise.py --continuous` (paper)
- one `codex_formalize.py --continuous` (lean)
- one `sync_with_auto_dev.py` loop wrapper (sync)

If any of the three is missing, **mention the absence in the same status report** and either restart it or escalate. Do not paper over a missing daemon by reporting only the closure totals — totals can keep climbing from one side alone (e.g. paper publishing closure_mark while lean has been dead for hours), and the user trusts your status replies to catch this.

Symptom that should always trigger an immediate `ps` check:

- **`paper=N>0, lean=0` for ≥30 min** in your hourly Round-SUCCESS counts. Paper proposing closure marks while lean produces zero rounds is the canonical signature of a dead lean orchestrator. Do not rationalize this as "work pool排空" without first verifying the lean process is actually alive — historical incident 2026-05-09: lean orchestrator naturally exited at 03:10 (`Session complete: 46 succeeded, 14 failed` after a PID-token swap), no one noticed for ~10h, multiple status replies kept saying "lean 端 work pool 长期排空" while the process was simply gone. Only the user's "并发数如何？" query at 13:10 prompted the `ps` that surfaced the outage.

The active error watch grep above now includes `Session complete:` / `draining N in-flight workers` / `Pipeline PID token is not current` so this signal arrives in the monitor as soon as it happens — but if you missed it or the monitor was offline, the per-status liveness probe is the safety net.

### Always run a second monitor: daemon liveness change watch

Log-stream monitors only see what the orchestrators *write* — when an orchestrator silently exits, its log goes quiet and the log-stream monitor produces zero events (silence ≠ healthy). Pair the active error watch with a second persistent monitor that polls `ps` every 60s and emits **only on liveness state change**:

```bash
prev=""
while true; do
  ps_out=$(ps -axo pid,ppid,command 2>/dev/null \
    | grep -E 'codex_revise\.py|codex_formalize\.py|sync_with_auto_dev\.py' \
    | grep -v grep || true)
  p=$(echo "$ps_out" | grep -c 'codex_revise\.py')
  l=$(echo "$ps_out" | grep -c 'codex_formalize\.py')
  s=$(echo "$ps_out" | grep -c 'sync_with_auto_dev\.py')
  pa=$([ "$p" -ge 1 ] && echo 1 || echo 0)
  la=$([ "$l" -ge 1 ] && echo 1 || echo 0)
  sa=$([ "$s" -ge 1 ] && echo 1 || echo 0)
  cur="paper=$pa lean=$la sync=$sa"
  if [ "$cur" != "$prev" ]; then
    ts=$(date '+%Y-%m-%d %H:%M:%S')
    if [ "$pa" -eq 0 ] || [ "$la" -eq 0 ] || [ "$sa" -eq 0 ]; then
      echo "[$ts] DAEMON DOWN — $cur (raw paper=$p lean=$l sync=$s; was: $prev)"
    else
      echo "[$ts] daemon liveness OK — $cur (raw paper=$p lean=$l sync=$s; was: $prev)"
    fi
    prev=$cur
  fi
  sleep 60
done
```

Compare alive-as-boolean (≥1 process matches → 1, else 0), not raw counts. The paper bash wrapper makes `codex_revise.py` match twice; the sync wrapper periodically spawns a Python child that pushes the sync count from 1 to 2 for a few seconds every 600s. Comparing raw counts emits a no-op `liveness OK` event every 10 minutes during steady state. Comparing alive-booleans stays silent and only fires when a daemon actually disappears.

`persistent: true`. Description: `BEDC daemon liveness change (paper/lean/sync)`.

The `[ "$cur" != "$prev" ]` guard means it stays silent during steady-state (one event at boot to confirm initial state, then nothing until a change). When a daemon dies, you get a `DAEMON DOWN` notification within 60s — the missing log signal becomes a positive `ps` signal.

Always run **both** monitors in parallel after starting the pipelines: log-stream (active error watch) + ps-based (daemon liveness change). The two cover orthogonal failure modes — log-stream catches loud failures (Tracebacks, recovery activity, `Session complete:` etc.); ps-based catches silent disappearance (process killed by OS, exit before flushing log, parent shell SIGHUP edge cases). Either alone misses an entire category.

Because Monitor no longer holds the orchestrator, you can freely change the `grep` filter, kill the Monitor, or re-launch it with a different filter without affecting any in-flight round.

## 3-hour open-ended self-check loop

While the pipelines run, register a 3-hour recurring self-check that asks open-ended questions about the project rather than a fixed metric checklist. Suggested invocation (the user types this once after pipelines start):

```
/loop 3h Open-ended self-check on BEDC pipelines (skill bedc-codex-auto-dev):
1. 项目运行的顺利吗？(both pipelines healthy, failure / conflict /
   cooldown rates, any stuck worker)
2. 有什么需要改进的？(recurring pattern in last ~50 commits, missing
   or over-tight gates, wasted effort like dedup / empty rounds /
   cooldown)
3. 数学品味如何？(sample 10 most recent merged commits per side;
   substantive vs shape-saturated bookkeeping; mechanical-arity /
   parameter-echo residue trend)
4. 有什么有意思的新发现？(skim last ~24h commits + capstones/; cite
   specific commits / chapters; concrete sentences not platitudes)
5. 如何进一步提升？(critical_path top-3 movement; banned chapter
   ready to leave SCHEMA_ONLY_HORIZONS; capstone count and quality;
   highest-leverage single change for math taste / throughput)
6. harness 还有什么提升空间？(Makefile precheck, subprocess lints,
   prompt HARD GATEs, orchestrator timeouts/parallel — where would
   a new gate prevent a recurring pattern, where would relaxing a
   gate save real rounds)

Make any harness/prompt adjustments authorized under the skill's
"Autonomous adjustment authority" without asking; for each, include
the trigger, file edited, version bump, commit SHA.

Report concisely (≤ 12 sentences): what's running, what changed since
last tick, what mattered, what you adjusted.
```

The 6 open-ended questions force a real read of recent work rather than a metric checklist that can pass while the project drifts. Concrete-sentence rule prevents platitude reports.

The user runs `/loop` once and the cadence is then automatic. Suggest it after the pipelines are healthy and observed for ~30 min. Cron auto-expires after 7 days; re-register if the run continues longer.

If the user prefers a single autonomous tick rather than recurring, they can also use `/loop` without an interval (dynamic pacing), in which case you self-pace via `ScheduleWakeup` between ticks. 3h is the right steady-state cadence; tighter only when a recent prompt change needs rapid iteration validation.

## Stop commands

For an orderly stop, run:

```bash
python3 $REPO/papers/bedc/scripts/codex_revise.py --stop
python3 $REPO/lean4/scripts/codex_formalize.py --stop
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

The merge path uses `git merge --no-ff --no-edit BASE_BRANCH` inside each round's worktree (rebase was retired 2026-05-04 in commit `35da139d5`). Round commits are preserved verbatim under a merge commit; conflict surface is a single-shot reconcile, not an N-commit replay.

- **`Merge conflict for codex-R<N> (attempt 1/2), invoking codex to resolve`**: codex is invoked with `prompts/conflict_resolve.txt` to resolve in-tree. If codex completes resolution, round continues; if not, round FAILs and worktree is retained for manual cleanup. With merge flow this is rarer than rebase was, but still happens when both sides genuinely edit the same theorem block.
- **`ff update of codex-auto-dev failed: hint: Diverging branches can't be fast-forwarded`**: this is now a **transient race** in `_ff_local_branch_to(wt_tip)` when a sibling worker pushed to origin between this round's merge step and its ff-update step. The push-retry loop (`fetch + merge --no-ff origin/<BASE> + push`) handles it; usually followed by `Round SUCCESS` within 1-2 seconds. **Not a real failure.** The previous rebase-flow's same-message error meant the round branch had diverged from BASE lineage and the round would FAIL; that semantics is gone now.
- **`Pre-merge hard gate failed: ... bedc_ci.py audit`** (Lean): means a sibling round landed a duplicate label or marker mismatch on BASE_BRANCH while this worktree was working. The script auto-routes to `_codex_resolve_post_rebase_audit` (kept its old name) to drop this round's colliding additions and retry the gate.
- **`Drift audit OK` followed by audit fail in paper merge**: paper's drift audit runs pre-merge inside the worktree, so it cannot see sibling-induced collisions until BASE is merged in. Same recovery path as above.
- **`3 consecutive failures — sleeping 180s`**: cooldown trigger. Look at the failing rounds' Phase B output files (`lean4/scripts/logs/codex/R<N>_phaseB_*.out.txt`); zero-byte means codex was killed externally (not a prompt issue), non-zero means inspect the gate that rejected it.

Modes the new merge flow eliminated entirely (do not appear anymore):

- **`Rebase left no own-round commit unique to BASE_BRANCH`** — codex's rebase resolution sometimes dropped the round's own work; merge can't drop a parent.
- **`Codex did not complete rebase, aborting`** with subsequent round FAIL — no rebase to abort.

### Hot-reload vs restart boundary

Edit-and-go (no pipeline restart needed; next round picks up the change):

| File | Role |
|---|---|
| `<repo>/.pipeline_parallel.json` | Live concurrency knobs: `paper`, `lean`, `lean_lake`. Read on every dispatch — edit and the next round respects the new value. |
| `lean4/scripts/prompts/phase_b.txt`, `phase_c.txt` | Lean target selection / implementation |
| `lean4/scripts/prompts/conflict_resolve.txt` | Lean codex-side merge conflict resolver |
| `lean4/scripts/prompts/post_rebase_audit_resolve.txt` | Lean codex-side audit recovery (legacy filename; now post-MERGE recovery) |
| `papers/bedc/scripts/prompts/phase_review.txt`, `phase_revise.txt` | Paper review / revise |
| `papers/bedc/scripts/prompts/conflict_resolve.txt` | Paper codex-side conflict resolver |
| `papers/bedc/scripts/prompts/post_rebase_audit_resolve.txt` | Paper codex-side audit recovery (legacy filename) |
| `lean4/NAMING.md` | Naming and decomposition discipline (referenced by phase prompts) |
| `lean4/scripts/critical_path.py` | Critical-path top-N discovery + per-call rolling cooldown + closureat-aware ranking (binary closed/open via `\closureat`, adaptive `deps_ready_threshold` 5→1 fallback) |
| `lean4/scripts/phase_d_lint.py` | Mechanical post-merge lints (called via subprocess from `run_phase_d_lints`) |
| `lean4/scripts/bedc_ci.py` audit / `--shape-saturation` | Drift + saturation + case-collision reports (called via subprocess) |
| `papers/bedc/preamble.tex` (`\closureat` macro) | Per-chapter closure marker; next pdflatex picks up. critical_path greps for `\closureat\{<X>Up\}\{<strength>Str\}` |
| `<repo>/.pipeline_parallel.json` | Live concurrency knobs `paper` / `lean` / `lean_lake` + `deps_ready_threshold` (default 5; clamp [1,20]). Read on every dispatch and on every critical_path call |

Restart-required (the long-running Python process loaded these at startup):

| Change | Affects |
|---|---|
| `lean4/scripts/codex_formalize.py` body (merge flow, retries, gate ordering, timeouts) | Lean pipeline |
| `papers/bedc/scripts/codex_revise.py` body (merge flow, retries, gate ordering, timeouts) | Paper pipeline |
| `--phase-b-timeout` / `--phase-c-timeout` / `--review-timeout` CLI defaults | Both |
| `--base-branch`, `--peer-sync-interval`, `--continuous`, `--resume` CLI flags | Both |

When you bump a phase-prompt version, edit BOTH files of that side together (`phase_b.txt` + `phase_c.txt`, or `phase_review.txt` + `phase_revise.txt`); the `## Prompts version` line gets mirrored into every commit body as `prompts: vN.M` so the trail is reconstructable.

### Recovery queue (catch-all worker recovery)

When any worker exits unsuccessfully with content commits in its worktree (merge-fail / pre-merge gate fail / Phase D lint fail / exception), `request_recovery(wt)` writes a JSON ticket to `.worktrees/.recovery_queue/` (lean) or `.worktrees/.paper_recovery_queue/` (paper) and notifies the **recovery consumer** thread. The consumer is a single-thread daemon spawned next to the existing builder/origin-sync threads in `main()`:

1. Picks oldest ticket (alphabetical sort by `R<N>_<ts>.json` / `P<N>_<ts>.json`).
2. Spawns codex inside the stuck worktree with `prompts/round_fallback_resolve.txt` — generic recovery instructions covering lake build / audit / merge conflict / stale marker / sync-merge-only / dirty tree.
3. On success retries `merge_worktree_to_base`. If that succeeds, the round merges as if nothing went wrong.
4. On failure moves ticket to `dead/` and force-removes the worktree + branch.

**Why this matters**: today's two pre-recovery cycles (R1948-R1955 SubgroupUp split spree, R2152/R2166/R2170 lake-build-after-cleanup) each required identical handling — codex investigates, drops the conflicting addition, retry merge. Wiring the catch-all into the main loop replaced ~20 lines of manual `git worktree remove` / cherry-pick rescue per session. Future failure patterns are handled by editing `prompts/round_fallback_resolve.txt` — no orchestrator code change needed.

Tickets persist on disk so the consumer resumes on orchestrator restart. Manual queueing is supported: drop a JSON file with the right shape into the queue dir and the consumer will pick it up on its next poll (30s).

### Closure marker (`\closureat`) and binary closed/open

A horizon is binarily CLOSED iff its chapter carries `\closureat{<X>Up}{<strength>Str}` (where `<strength>` ∈ `checkedCert` / `bridgeCert`) somewhere in its include closure. The macro lives in `papers/bedc/preamble.tex` and renders a visible `Theory closed: AcceptGate(NameCert_<X>Up)(<strength>)` line in the PDF. `critical_path.py` greps for it (regex `\\closureat\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}\{\s*\\(\w+)Str\s*\}`) and excludes closed chapters from `top` so codex stops attacking them.

Paper rounds add the marker via `kind = "closure_mark"` (phase_review.txt v2.6+). The reviewer scans `top` for chapters whose every NameCert clause is `\leanchecked` to a real Lean target; one-line revise round adds `\closureat{<X>Up}{\checkedCertStr}` at the chapter end. **Closure proposals always rank ahead of new theory_extension targets for the same chapter** — closing is the highest-leverage way to retire a horizon and free Phase B for fresh fronts.

The first chapter closed today: `BoolUp` (paper P1859, 2026-05-04). Track progress with `python3 lean4/scripts/critical_path.py | jq '.closed_horizons, .open_horizons'`.

### Critical-path mechanism

`lean4/scripts/critical_path.py` ranks every horizon `<X>Up` chapter under `papers/bedc/parts/concrete_instances/`. Sort key:

```
(-downstream, -downstream/(1+thms), name)
```

after excluding (a) nodes binarily CLOSED (chapter has `\closureat{<X>Up}{\checkedCertStr|\bridgeCertStr}`); (b) nodes whose declared deps have `< deps_ready_threshold` implementations (default 5, tunable via `.pipeline_parallel.json` key `deps_ready_threshold`; auto-relaxes 5→1 when strict yields empty top, emitting `deps_ready_relaxed: true`); (c) `SCHEMA_ONLY_HORIZONS` (chapters whose paper schema is parametric — currently `totalorder`, `preorder`, `poset`). The top-3 entries are the next fronts the library should attack. JSON output also includes `closed_horizons={checkedCert: N, bridgeCert: M}` and `open_horizons` for at-a-glance progress.

Phase B HARD GATE: at least 1 of 3 selected targets must come from `top[0..2]`. The fallback "if technically blocked, use top[3..]" is mechanised — a node counts as blocked only when all three of (a) the chapter's paper schema has < 3 `\begin{definition}` blocks, (b) implementation needs an inductive / import that does not yet exist anywhere under `lean4/BEDC/`, (c) `critical_path.py` reports `deps_ready = false` (always false for nodes IN `top` by construction). A single-condition rationalisation is invalid.

If all three top-3 nodes claim blocked under that conjunction, codex emits `{"targets": []}`. Empty rounds are preferred over silent fallback to depth-refinement of saturated horizons.

Run `python3 lean4/scripts/critical_path.py | jq '.top[:3]'` any time to see what the next targets should be.

### Phase D mechanical lints

`lean4/scripts/phase_d_lint.py` runs after lake / check-axioms / audit / axiom-purity, before merge. Three checks against declarations introduced in the round (`<base-branch>..HEAD` under `lean4/BEDC/`):

1. **Mechanical-arity suffix.** New name matching `_(two|three|four|five|six)(?:_step)?(?:_witness_chain)?\b` is rejected. NAMING.md §3.
2. **Parameter-echo schema.** Signature contains `(name : ∀ … hsame …)` binding AND the conclusion is also `forall … hsame …` AND the conclusion has no other BHist anchor (post `hsame` + bare `BHist` strip). All three together — the hypothesis bind alone is a legitimate hsame-stability assumption, and an embedded `forall x', hsame …` inside a single-valuedness uniqueness clause is also legitimate when the conclusion mentions a derived classifier/carrier (Empty / e0 / e1 / Cont / NameCert / DescentCertificate / …). False positives cost a real Lean round, so keep the conclusion-aware check tight.
3. **BHist-anchor for Derived theorems.** Every new declaration under `BEDC.Derived.*` must mention at least one concrete BEDC kernel symbol. Current accepted set: `BHist | BMark | Empty | e0 | e1 | cons | append | sameSig | ProbeBundle | SigRel | InGap | NameCert | SemanticNameCert | Pkg | hsame | msame | Cont | Ext | InBundle | SameSig | UnaryHistory | StageInterface | SealEvent | SealInterface | AskEvent | AskPolicy | BundleAskPolicy | DescentCertificate | StableTransformation | ThreadFamily | bundleAppend | bundleLength | bwordLength`. When a new kernel structure is added under `lean4/BEDC/FKernel/`, append it to `BHIST_CONSTRUCTOR_RE` — otherwise legitimate `<X>NameCert`-style theorems hit a `\bNameCert\b` non-match because of the prefix and get rejected.

Stale-marker check (separate, in `codex_formalize.py::detect_markers_not_backed_by_new_decls`): a `\leanchecked|leanstmt|leandef{X}` added to paper this round must reference some declaration X that exists *anywhere* under `lean4/BEDC/` — not only declarations introduced in this round. The new helper `_collect_all_lean_declarations` enumerates every fully-qualified name. The earlier "must be in this round's diff" rule rejected legitimate paper-catchup rounds where a Lean declaration finalized earlier finally gets its marker registered.

Phase D failure routes through the same `(ok, gate_name, tail)` channel as audit failures and is not auto-recovered — the round is marked FAILED and the worktree is removed. To tighten any of the three regexes, edit `phase_d_lint.py` and the next round picks up the change.

Predict-before-merge: run `python3 lean4/scripts/phase_d_lint.py --worktree /tmp/<commit-test> --base-branch <commit>^` against a candidate commit checkout to see exactly which lint catches it.

### Schema-only horizons (algebra parametric ban)

`lean4/scripts/critical_path.py` excludes a fixed set from `top` because their paper schemas write laws as parametric operators (`mul / add / neg : BHist -> BHist -> BHist` left abstract). A Lean round picking such a horizon can ONLY produce `(name : forall x y z, hsame …)` parameter-echo schema, which Phase D mechanically rejects:

```python
SCHEMA_ONLY_HORIZONS = {
    "abgroup", "group", "monoid",
    "ring", "commring", "field",
    "module", "vecspace", "linearmap", "matrix",
    "polynomial", "fps",
    "lattice", "totalorder", "preorder", "poset",
}
```

`phase_b.txt` v3.6+ also enumerates the same set under "Schema-only horizons HARD BAN" so codex sees the constraint at target-selection time, not just as a passive filter on `top`. When you observe a Lean round selecting a target whose `paper_target_chapter` matches `papers/bedc/parts/concrete_instances/*_<banned>_*.tex`, it's a prompt-comprehension regression — re-state the rule in `phase_b.txt`, bump the version, and the next round picks it up.

Removing a chapter from the ban requires the paper side to first add a *concrete* `mul := λ h k => …` definition (BHist-valued, not abstract) so the resulting Lean target has BHist-anchored content rather than a forall-hsame echo.

### Honest taste audit (what to actually look at)

Net headcounts (added − deleted) over a recent window are not enough — codex can drive the headline numbers up with parameter-echo schema or trivial-special-case theorems. After every ~20 rounds, sample the actual statements:

```bash
# 1. New decl names, with derivative-domain origin if any
git log --since='12 hours ago' --no-merges -p -- 'lean4/BEDC/' \
  | grep -E '^\+(theorem|lemma|def)\s+[A-Za-z_]+' | head -40

# 2. Saturated shape family — should NOT be growing once shape-saturation > 3
python3 lean4/scripts/bedc_ci.py audit --shape-saturation

# 3. Critical-path top — top-3 thms should be moving
python3 lean4/scripts/critical_path.py | jq '.top[:5]'

# 4. NAMING residue — should be flat or shrinking, never growing
grep -rE 'theorem\s+\w+_(two|three|four|five|six)\b' lean4/BEDC/ | wc -l

# 5. Parameter-echo residue under Derived (Phase D should keep this near 0
#    for new decls; existing instances may persist):
grep -rE '\(\s*\w+\s*:\s*(∀|forall)[^)]*hsame' lean4/BEDC/Derived/ | wc -l
```

The honest question is not "did declarations grow" but "did declarations referencing concrete BEDC kernel constructs grow, did the critical-path top-3 actually move, did NAMING residue stay flat or shrink, did parameter-echo-under-Derived not regrow."

Lean-side declaration count divided by paper-side label count is a useful ratio: ~1.5x is normal because one paper theorem often corresponds to 2-3 Lean lemmas plus helpers. Above ~3x usually means the lean side is producing scaffolding-only or parameter-echo growth that the paper side has not asked for.

### Oversize tex split (now self-healing)

`papers/bedc/Makefile` calls `bash scripts/check_tex_size.sh` as a `precheck` prerequisite before the two `pdflatex` runs. The script exits non-zero with a clear `OVERSIZED .TEX` message naming each .tex over 800 lines. Codex sees that during its own Step 2 build and self-heals (split at section boundary, sibling/child file, parent appends `\input{...}`, rerun make) before commit. The pipeline's `run_pdf_build` wraps the same `make`, so it's also second-line protection.

You should not be hand-splitting .tex files anymore. If you observe an `OVERSIZED .TEX` failure that codex did not self-heal, that's either:

- the wrapper script is broken (run `bash papers/bedc/scripts/check_tex_size.sh` to verify), or
- codex is on its first-ever encounter with the gate and isn't reading stderr — add a one-line nudge in `phase_revise.txt` Step 2.

Field examples from the manual era (kept for reference; the gate now does this automatically):

- `option/02_tagged_option_namecert.tex` (804 lines) → `02_*` (487) + `02b_option_certificate_chains.tex` (317)
- `34_continuous_namecert_construction.tex` (843) → `34_*` (329) + `34b_continuous_certificate.tex` (514)
- `35_compact_namecert_construction.tex` (802) → `35_*` (465) + `35b_compact_certificate.tex` (337)
- `08_option_namecert_construction.tex` (807) → `08_*` (215) + `option/09_composite_image_classifier_public_readback.tex` (592)

### Autonomous adjustment authority

While monitoring, you have standing authority to make harness/prompt adjustments without asking, when ALL of the following hold:

1. The change is **purely additive or a tightening of an existing rule** (new HARD GATE, narrower regex, removing a chapter from a ban list because the unblock condition is met). Not changing the merge flow, not relaxing safety gates.
2. The trigger is **a recurring pattern, not a one-off**: ≥ 2 commits / rounds exhibiting the same problem, or a paper-side state change (e.g. a banned chapter just got its concrete instance) whose downstream effect is mechanical.
3. The change is **scoped**: hot-reloadable files (prompts under `lean4/scripts/prompts/` or `papers/bedc/scripts/prompts/`, subprocess scripts under `lean4/scripts/` or `papers/bedc/scripts/`, `papers/bedc/scripts/check_tex_size.sh` and friends, `lean4/scripts/critical_path.py` constants) are the cheap default. Orchestrator-body edits (`codex_revise.py` / `codex_formalize.py`) and pipeline restarts are also in scope when justified — see "Pipeline restart policy" below.
4. The change is **traceable**: bump the relevant `## Prompts version` so commit bodies record `prompts: vN.M`; commit and push to `codex-auto-dev` immediately so in-flight rounds can ff-update.

When making an autonomous change:

- Briefly state the trigger (one or two sentences) before the edit so the user can roll back after.
- Make the edit, run any verification (smoke test, `bash papers/bedc/scripts/check_tex_size.sh`, `python3 lean4/scripts/critical_path.py | jq '.top'`), commit + push.
- Note the change in your reply with the commit SHA so the user can roll back if needed.

### Pipeline restart policy

**Operate fully unattended — never pause to ask whether to restart. Restart only when necessary.** Necessary means:

- An orchestrator-body change (`codex_revise.py` / `codex_formalize.py`) was just committed and the new behaviour is needed for in-flight or upcoming rounds.
- The pipeline has wedged (no `Round SUCCESS` or `FAILED` event for >30 min while >1 worker should be active, processes stuck in uninterruptible IO, etc.).
- The user explicitly asked.

NOT necessary (do not restart):

- Swapping a Monitor `grep` filter to reduce noise. Monitors are now decoupled from the orchestrator (background-launched via nohup, see "Start (background, detached)") — kill or re-launch the Monitor freely.
- A prompt or `critical_path.py` constant change. Those are hot-reloaded by next round dispatch.
- A `.pipeline_parallel.json` edit (paper / lean / lean_lake concurrency). Re-read on every dispatch.
- A single round failure or a transient `ff update of codex-auto-dev failed: Diverging branches can't be fast-forwarded` race during merge push retry — self-recovers within 1-2 seconds via the orchestrator's fetch+merge+push retry loop.

When restart IS necessary, prefer the orderly path: commit + push the change first, then `python3 …codex_revise.py --stop` and `python3 …codex_formalize.py --stop`, wait for drain, then relaunch via the **background start commands above** (nohup + disown — never via a Monitor). Run the two-step check from "Verify restart success" — `ps` for `PPID=1`, then a one-shot `tail -3` on each log to confirm log lines are advancing. Persistent `tail -F` does NOT count as restart verification; it blocks forever if the orchestrator died at startup and never notifies. In-flight worktrees survive on disk; paper resumes via `--resume`, lean's `--continuous` re-dispatches.

Still NOT in autonomous scope (always ask):

- Loosening a HARD GATE (would need a concrete false-positive trace plus user sign-off).
- Changing `.pipeline_parallel.json` keys (`paper` / `lean` / `lean_lake`) or `--phase-*-timeout` CLI defaults (resource budget belongs to the user).

Frequency discipline: even with authority, do not edit prompts faster than the pipeline can produce signal. Wait at least 30 commits or 1 hour after a prompt bump before another edit on the same file, unless the new prompt is producing immediate misbehaviour. Edit churn confuses codex.

Concrete autonomous-action examples this skill has handled:

- Removing chapters from `SCHEMA_ONLY_HORIZONS` once paper-side concrete instances landed (paper P699-P712 unlocked monoid/group/abgroup/ring/commring/field; updated `critical_path.py` constant + mirror in `phase_b.txt` BAN section without asking).
- Tightening `phase_d_lint.py` parameter-echo to be conclusion-aware after R1261/R1262 false positives.
- Splitting an oversized `.tex` file (now superseded by Makefile precheck — codex self-heals).
- 2026-05-04 commit `651cb017d`: case-collision audit. Added `detect_case_collision_paths()` to `bedc_ci.py audit` after a `Singleton…NonZero.lean` vs `Singleton…Nonzero.lean` index dup wedged macOS APFS for several rounds. Future occurrences self-heal.
- 2026-05-04 commit `3af7dd36d`: shared critical-path lock. Anchored `LOCKS_FILE` to `git rev-parse --git-common-dir` so all worktrees see one lock at `<repo>/.git/bedc-critical-path-locks.json`. Eliminated the dedup pile-up where 10+ rounds picked identical top-1.
- 2026-05-04 commit `35da139d5`: rebase → merge. Replaced `git rebase BASE` with `git merge --no-ff --no-edit BASE` in both orchestrators' `merge_worktree_to_base`. Eliminated the "Diverging branches" / "no own-round commit" / "Codex did not complete rebase" round-FAIL modes — observed 0 hard FAILs in the 30-min window after restart vs ~5 hard FAILs in the equivalent window before.
- 2026-05-04 commit `8c156773c`: phase_revise v2.4 dropped Step 5 "Re-sync with remote before commit" (the `_git_lock`-serialised pipeline guarantees origin doesn't move during a revise; Step 5's merge-commit was pure noise). Paper rounds went from 3 commits/round to 2.
- 2026-05-04 commit `9247e53d6`: critical_path adaptive `deps_ready_threshold` — JSON-tunable + auto-relax 5→1 when strict yields empty. Eliminates the wedged-empty-top failure mode (1.5h × 22 cooldowns burned earlier in the day because `field` had `commring=4 < 5`).
- 2026-05-04 commit `d621801d6`: catch-all recovery queue + consumer thread on both pipelines. Any worker FAIL with content commits → ticket → background codex investigates + retries merge → SUCCESS or marks dead. Replaces ~20 lines of manual `git worktree remove` / cherry-pick rescue per session.
- 2026-05-04 commit `6d9b6c1b7`: `\closureat` binary closure end-to-end. preamble macro + phase_review v2.6 / phase_revise v2.6 `closure_mark` target kind + critical_path closure-aware ranking (drops the heuristic `thms >= 10` cap in favor of explicit AcceptGate certification). First chapter closed: BoolUp (P1859, same day).
- 2026-05-04 commit `8099c89de`: fix CLOSUREAT_RE greedy bug — first-pass regex captured `t` instead of `checkedCert` because `[^}]*\\?(\w+)Str` was greedy past the leading backslash. Tighter regex `\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}\{\s*\\(\w+)Str\s*\}` is whitespace-tolerant + accepts both `\BoolUp` and `BoolUp`.
- 2026-05-04 commit `574fb6863`: NAME_RE accept underscores so `46_zeta_basic_namecert_construction.tex` resolves to canonical `zeta_basic` instead of literal-filename horizon (had been polluting `top` with malformed entries like `file_lean=46ZetaBasicNamecertConstruction.texUp.lean`).
- 2026-05-05 commit `610751890`: phase_b v5.7 → v5.8 / phase_review v3.1 → v3.2. Removed grade-axis `(none) → ...` skip rule that wedged 64/66 grade=null open chapters (lean side wouldn't pick a chapter without `closurestatus` block; paper side wouldn't propose one because `next_axis` algorithm defaulted to `formal_status`). Both prompts now treat null grades as normal work.
- 2026-05-06 commit `09925c910`: critical_path `top_root_unblocks` field + phase_review v3.3 root-unblock HARD GATE. After bedc-deep merged 200+ external chapters whose dep tree roots (banach / fieldext / topology / manifold / finset) were thms=0 paper stubs, ~145/205 open chapters became dep-blocked. New `compute_root_unblocks(threshold)` enumerates chapters whose `thms < threshold` are SINGLE-blocker for ≥1 downstream; phase_review HARD GATE forces 1 of N targets to attack the highest-leverage entry.
- 2026-05-06 commit `e2e2d7391`: critical_path `recent_attack_threshold=3` rotation in `top_root_unblocks`, then `4c41cbd8e` tightened to `recent_attack_threshold=1` + added `_inflight_paper_attack_chapters()` scanning `.worktrees/paper_P*/` for uncommitted edits. With paper=8 concurrent and ~10 root candidates, the v3.3 HARD GATE pulled all paper rounds into the same `top_root_unblocks[0]` (manifold dogpile: 18/30 targets in a 2h window). codex writes deterministic obligation labels for the same chapter+task prompt, so even 2 simultaneous rounds produce identical `\label{thm:<chapter>-...}` collisions. Threshold=1 + in-flight scan ensures concurrent rounds spread across distinct roots.
- 2026-05-06 commit `4e2a4d8a9`: `deps_ready` uses `max(thms, labels)` instead of just `thms`. Paper rounds were writing rich obligation surfaces (e.g. bundle: 9 `\begin{theorem}` + 9 `\label`) but no `\leanchecked` markers yet, so `dep.thms` stayed 0 and downstream chapters stayed dep-blocked despite the chapter being paper-ready. New `extract_horizons` field `labels` counts paper obligation labels in chapter's full include closure; `deps_ready` treats EITHER threshold-crossing as ready. Result: top_size jumped 8 → 25 within one tick.
- 2026-05-06 commit `a21fc21d2`: `auto_tune_concurrency` LEAN_BUFFER 3 → 0. With `lean = top_size + 3`, when supply was tight (top_size=7 / lean=10) the 3 extra workers necessarily picked overlapping chapters, producing dup-decl lake-build failures (NumFieldUp / FieldExtUp). `lean = top_size` makes worker count exactly match supply; sibling claim lock keeps them non-overlapping. Lean grows with paper unblocks.
- 2026-05-06 commit `1d12c4fad`: phase_c v5.8 → v5.9 added "target-exclusive theorems (HARD GATE)". After R3045/R3049 produced identical 6-error SHALLOW GROWTH from codex writing parameter-echo neighbor theorems (`BHistCarriesOpen_classifier_transport` + 4 `BHist*_classifier_transport` siblings), prompt now mandates every new declaration must be a Phase B target, target-helper, or `<target>_<suffix>` prereq. Concrete BHist*_classifier_transport rejection example included.
- 2026-05-06 commit `fa0334da2`: lean conflict_resolve.txt deletion-aware rule. After my fix `f23474528` (deleting stuck dup `TopologySingleton_boundary_open_laws`) was reverted by R3058's merge resolution (codex kept "ours" = older version with deleted theorem still present), prompt now explicitly says: deletion in BASE is deliberate cleanup, prefer the deletion side over "keep both".
- 2026-05-06 commit `a075c2ef0`: `tools/auto_heal_base.py` daemon (15min cycle). Detects stuck dup paper labels via `bedc_ci.py audit`, invokes codex with canonical-site rules to remove the redundant copy, commits + pushes. Without this, manual surgery is the only path out of audit-fail / cooldown loops on BASE-stuck dups (observed: 9 cooldowns × 180s + 36 SHALLOW lints / 30 min before manual delete of `_diffform_derham_boundary_consumption.tex` and `TopologySingleton_boundary_open_laws`).

### When manual BASE surgery is still needed (auto-heal limits)

`auto_heal_base.py` covers `bedc_ci.py audit` dup labels. It does NOT cover:

1. **Dup-conclusion theorem stuck on BASE**: `phase_d_lint.py::detect_shallow_growth_patterns` only scans round-added decls (it diffs `<base-branch>..HEAD`), so a BASE-resident pair doesn't appear in any single round's diff but every round's merge re-introduces the lint when its added theorem has a conclusion that overlaps with one already there. Symptom: 5+ rounds in 30 min reporting the same `SHALLOW GROWTH PATTERN: ... duplicate theorem conclusion in <A> and <B>` where neither A nor B is in the round's own diff. Manual fix: delete one declaration in main checkout, inline its uses where needed, lake build, commit, push. Future improvement: extend `detect_shallow_growth_patterns` to scan `lean4/BEDC/` instead of just `<base>..HEAD`, and let `auto_heal_base.py` invoke codex on a finding.

2. **In-flight rounds dispatched against stale BASE / stale prompt**: when you push a fix targeting a known stuck pattern, in-flight rounds (10-30 minutes deep into Phase B/C) still carry the old BASE in their worktree. Their merge-resolution may RE-INTRODUCE the just-deleted item via "keep both" (the conflict_resolve.txt deletion-aware rule mitigates but doesn't eliminate). If lean SUCCESS rate stays ≤1/30min and `[cooldown] 3 consecutive failures` keeps firing, the in-flight pool is poisoned. Resolution: stop the lean orchestrator (`python3 lean4/scripts/codex_formalize.py --stop`), wait 30s, force-kill any lingering codex children (`pkill -TERM -f 'codex exec.*round_R'`), force-kill the orchestrator if `--stop` didn't drain (`pkill -TERM -f codex_formalize.py`), then relaunch fresh. New round dispatch will use the new BASE + new prompt. Cost: lose in-flight rounds' codex compute (~30 min × N workers), but their success rate against poisoned BASE is near 0 anyway. Paper orchestrator usually doesn't need restart unless the same poisoning is hitting paper labels.

3. **Stale paper marker referencing removed lean target**: `auto_heal_base.py` doesn't yet detect `unresolved Lean markers` audit reports. When `bedc_ci.py audit` reports `[bedc-ci] unresolved Lean markers: papers/bedc/parts/.../X.tex:N leanchecked -> BEDC.<...>.<name>` and `<name>` is missing under `lean4/BEDC/`, the marker either references a not-yet-implemented target (legitimate pending work) or a deleted target (real stale). Distinguishing requires checking whether any round commit deleted the named declaration recently. Manual triage for now.

### Harness design principles

When the workflow keeps surfacing the same issue, the gate lives at the wrong level. Move it down. Levels of correctness enforcement, in preferred order:

1. **Build gate (Makefile precheck)** — the script that produces the artifact (PDF, lake build) refuses to run when an invariant breaks. Codex sees the failure in normal Step 2 and self-heals before commit. Generic, no theme-specific logic. Example: `papers/bedc/scripts/check_tex_size.sh` invoked by `Makefile`.
2. **Subprocess lint (hot-reloadable)** — `phase_d_lint.py`, `critical_path.py`, `bedc_ci.py audit --shape-saturation`. The orchestrator calls these via subprocess on each round, so edits take effect without restart. Use for mechanical pattern checks (regex on signatures, constraint-set membership, label uniqueness).
3. **Prompt HARD GATE (hot-reloaded)** — Phase B/C/Review/Revise prompts. Bumping `## Prompts version` mirrors into commit bodies for traceability. Use for guidance that needs codex's judgment but is articulable as a rule. Lower confidence than levels 1-2 because codex occasionally violates prompts.
4. **Long-running script body (restart-required)** — `codex_revise.py`, `codex_formalize.py` orchestrator body. Use for the merge flow itself, retry policy, gate ordering, default timeouts. Restart cost is the in-flight rounds drained.

When a gate fires unexpectedly (false positive), run it offline against the failed commit before tightening or relaxing it:

```bash
git -C $REPO worktree add /tmp/test <commit>
python3 lean4/scripts/phase_d_lint.py --worktree /tmp/test --base-branch <commit>^
git -C $REPO worktree remove /tmp/test
```

False-positive cost is real: rejecting a legitimate Lean round wastes ~10 min of codex work + lake build, and the same pattern may recur. Prefer narrower (more context-aware) checks over looser thresholds. Concrete narrowing patterns: conclusion-aware regex (parameter-echo only fires when conclusion *also* has forall-hsame), strip-and-rescan (after dropping `hsame` and bare `BHist`, look for any other anchor), exists-anywhere lookup (stale-marker check searches all of `lean4/BEDC/`, not just this round's diff).

### Mathematical taste checklist

Net theorems added does NOT measure theory growth. After every ~30 rounds, sample the actual statements:

| Signal | Detect | Verdict |
|---|---|---|
| Parameter-echo schema | Hyp `(name : forall … hsame …)` AND concl `forall … hsame …` AND no other BHist anchor in concl | Bookkeeping, not theory |
| Mechanical-arity suffix | `_(two\|three\|four\|five\|six)` | Naming repeating shape, not new concept |
| Shallow growth | New carrier `def` with no theorem invoking it | Carrier-only growth |
| Duplicate theorem conclusion | New `_single_valuedness` AND `_nonempty_equivalence` with same hypotheses | Mutually-implying twin |
| Schema-only horizon | Target chapter's paper schema is parametric (no concrete BHist-valued operator) | Physically can't anchor; ban from `critical_path` |
| Register-only round | Paper diff is whitespace + new markers; lean diff is empty | Maintenance, not work |
| Same-file saturation | ≥3 consecutive commits in same file with `_alt`/`_with_fields`/`_source_equivalence` siblings | Lazy depth refinement |

Counts that don't lie:

- `python3 lean4/scripts/critical_path.py | jq '.top[:3]'` — top-3 `thms` field should move up over a 30-round window.
- `python3 lean4/scripts/bedc_ci.py audit --shape-saturation` — flat or shrinking, never growing.
- `grep -rE 'theorem\s+\w+_(two|three|four|five|six)\b' lean4/BEDC/ | wc -l` — flat or shrinking.
- `grep -rE '\(\s*\w+\s*:\s*(∀|forall)[^)]*hsame' lean4/BEDC/Derived/ | wc -l` — flat or shrinking.

Lean-decl / paper-label ratio: ~1.5x normal (one paper theorem ≈ 2-3 Lean lemmas + helpers). Above ~3x means lean side is producing scaffolding-only growth the paper hasn't asked for.

### Gate evolution path (how a problem becomes a rule)

1. Observe the problem in 1-2 commits. Note the precise pattern.
2. Try the cheapest fix first: prompt rule. Hot-reload, bump `## Prompts version`.
3. If the prompt rule keeps being violated (≥ 2 more occurrences), promote to subprocess lint regex. Test against failing commits to confirm catch + against known-good commits to confirm no false positive.
4. If the lint produces false positives, narrow with context (conclusion-aware, anchor strip, exists-anywhere lookup) — do not loosen the threshold.
5. If the problem is structural (e.g. paper schema is parametric, can't ever produce anchored Lean), exclude at the source: `critical_path.py` constants, plus an explicit ban in the relevant prompt mirror.
6. If the problem is environmental (e.g. .tex line cap), push the gate into the build itself (Makefile precheck), so the artifact-producing step refuses.

Concrete evolution traces from this codebase:

- **Parameter-echo**: prompt v3.4 → `phase_d_lint.py` regex → conclusion-aware regex → BHist+hsame strip before scan.
- **Schema-only horizons**: lint catching the symptom → `SCHEMA_ONLY_HORIZONS` filter in `critical_path.py` → `phase_b.txt` v3.6 explicit BAN section.
- **Oversize tex**: hand-splits on Claude side → `phase_review.txt` 760-line threshold → `phase_revise.txt` Step 0.5 abort → `Makefile` precheck (root cause, codex self-heals).
- **Stale marker**: strict "must be in this round's diff" → relaxed "must exist anywhere in `lean4/BEDC/`" via `_collect_all_lean_declarations` (false-positive fix).
- **Phase B prompt obsession with abgroup/group**: prompt soft fallback → critical_path filter → prompt explicit BAN with example rejected shape.

### Fast triage commands

Quality:
```bash
git -C $REPO log --oneline codex-auto-dev | head -20
python3 $REPO/lean4/scripts/bedc_ci.py audit
python3 $REPO/lean4/scripts/bedc_ci.py audit --shape-saturation
python3 $REPO/lean4/scripts/critical_path.py | jq '.top[:5]'
```

Merge:
```bash
ps -axo pid,etime,command | grep -E 'codex_revise|codex_formalize' | grep -v grep
git -C $REPO worktree list
git -C $REPO status --short  # MUST be empty while rounds are merging
```

Phase D dry-run on a worktree (predict what the lint will say without merging):
```bash
python3 $REPO/lean4/scripts/phase_d_lint.py \
  --worktree $REPO/.worktrees/round_R<N> \
  --base-branch codex-auto-dev
```

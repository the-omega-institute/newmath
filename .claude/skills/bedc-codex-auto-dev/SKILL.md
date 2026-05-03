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

## Start (background, detached)

**Always launch the orchestrators as fully-detached background processes — never inside a `Monitor` and never piped through anything that the harness owns.** The orchestrator must outlive any Claude Code session, Monitor swap, or filter change. Use `nohup … &` plus `disown` so the process re-parents to PID 1 and survives shell exit.

Use the `Bash` tool. Do **not** also pass `run_in_background: true` — `nohup … &` + `disown` already detaches; double-backgrounding only confuses cleanup.

Paper:

```bash
mkdir -p /Users/chronoai/newmath/papers/bedc/scripts/logs && \
nohup bash -c '
  python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py \
    --base-branch codex-auto-dev --resume && \
  python3 /Users/chronoai/newmath/papers/bedc/scripts/codex_revise.py \
    --base-branch codex-auto-dev --parallel 5 --continuous --peer-sync-interval 0
' >> /Users/chronoai/newmath/papers/bedc/scripts/logs/orchestrator.log 2>&1 &
disown
```

Lean:

```bash
mkdir -p /Users/chronoai/newmath/lean4/scripts/logs && \
nohup python3 /Users/chronoai/newmath/lean4/scripts/codex_formalize.py \
  --base-branch codex-auto-dev --parallel 5 --continuous \
  --lake-parallel 1 --phase-b-timeout 3600 --phase-c-timeout 4500 \
  >> /Users/chronoai/newmath/lean4/scripts/logs/orchestrator.log 2>&1 &
disown
```

Immediately after launching, confirm both processes are alive and re-parented:

```bash
ps -axo pid,ppid,pgid,etime,command | grep -E 'codex_revise.py|codex_formalize.py' | grep -v grep
```

`PPID` should be `1` (init) — that's the proof that nohup detached cleanly. If `PPID` is your shell's PID, the disown didn't take and a session exit will SIGHUP the orchestrator.

Tune `--parallel` upward (3 → 5 → 7) only when phase B is consistently completing well under the timeout (otherwise rebase conflicts and codex-API contention eat the gain). `--phase-b-timeout` and `--phase-c-timeout` defaults (2700 / 3600) are too tight under parallel ≥ 5: bump to 3600 / 4500. The lake gate stays at `--lake-parallel 1` regardless — multiple concurrent `lake build` exhaust memory.

## Monitor (read-only, never owns the orchestrator)

Monitors `tail -F` the log files the detached orchestrators write to. They are pure observers — killing, swapping, or re-launching a Monitor never touches the orchestrator process.

Paper monitor:

```bash
tail -F /Users/chronoai/newmath/papers/bedc/scripts/logs/orchestrator.log \
  | grep -E --line-buffered 'SUCCESS|FAILED|ERROR|WARNING|Exception|Traceback|Push rejected|Rebase conflict|Merging|Merged|P[0-9]+'
```

Lean monitor:

```bash
tail -F /Users/chronoai/newmath/lean4/scripts/logs/orchestrator.log \
  | grep -E --line-buffered 'SUCCESS|FAILED|ERROR|WARNING|Exception|Traceback|Push rejected|Rebase conflict|Merging|Merged|builder|PASS|FAIL|R[0-9]+'
```

Use `persistent: true` for both. Describe them as:

- `BEDC paper pipeline log on codex-auto-dev`
- `BEDC Lean pipeline log on codex-auto-dev`

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

### Hot-reload vs restart boundary

Edit-and-go (no pipeline restart needed; next round picks up the change):

| File | Role |
|---|---|
| `lean4/scripts/prompts/phase_b.txt`, `phase_c.txt` | Lean target selection / implementation |
| `lean4/scripts/prompts/conflict_resolve.txt` | Lean codex-side rebase conflict resolver |
| `lean4/scripts/prompts/post_rebase_audit_resolve.txt` | Lean codex-side audit recovery |
| `papers/bedc/scripts/prompts/phase_review.txt`, `phase_revise.txt` | Paper review / revise |
| `papers/bedc/scripts/prompts/conflict_resolve.txt` | Paper codex-side conflict resolver |
| `papers/bedc/scripts/prompts/post_rebase_audit_resolve.txt` | Paper codex-side audit recovery |
| `lean4/NAMING.md` | Naming and decomposition discipline (referenced by phase prompts) |
| `lean4/scripts/critical_path.py` | Critical-path top-N discovery (called via subprocess from Phase B) |
| `lean4/scripts/phase_d_lint.py` | Mechanical post-rebase lints (called via subprocess from `run_phase_d_lints`) |
| `lean4/scripts/bedc_ci.py` audit / `--shape-saturation` | Drift + saturation reports (called via subprocess) |

Restart-required (the long-running Python process loaded these at startup):

| Change | Affects |
|---|---|
| `lean4/scripts/codex_formalize.py` body (merge flow, retries, gate ordering, timeouts) | Lean pipeline |
| `papers/bedc/scripts/codex_revise.py` body (merge flow, retries, gate ordering, timeouts) | Paper pipeline |
| `--phase-b-timeout` / `--review-timeout` defaults | Both |

When you bump a phase-prompt version, edit BOTH files of that side together (`phase_b.txt` + `phase_c.txt`, or `phase_review.txt` + `phase_revise.txt`); the `## Prompts version` line gets mirrored into every commit body as `prompts: vN.M` so the trail is reconstructable.

### Critical-path mechanism

`lean4/scripts/critical_path.py` ranks every horizon `<X>Up` chapter under `papers/bedc/parts/concrete_instances/`:

```
score = transitive_downstream_horizons / (1 + thms)
```

after excluding nodes that are saturated (`thms >= SATURATION_THRESHOLD`, currently 10) or whose declared dependencies have `< DEPS_READY_THRESHOLD` (currently 5) implementations. The top-3 entries are the next fronts the library should attack.

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
- A single round failure or a transient `ff update` race. Self-recovers.

When restart IS necessary, prefer the orderly path: commit + push the change first, then `python3 …codex_revise.py --stop` and `python3 …codex_formalize.py --stop`, wait for drain, then relaunch via the **background start commands above** (nohup + disown — never via a Monitor). Verify with `ps -axo pid,ppid,pgid,etime,command | grep -E 'codex_revise.py|codex_formalize.py' | grep -v grep` that the new processes have `PPID 1`. In-flight worktrees survive on disk; paper resumes via `--resume`, lean's `--continuous` re-dispatches.

Still NOT in autonomous scope (always ask):

- Loosening a HARD GATE (would need a concrete false-positive trace plus user sign-off).
- Changing `--parallel` / `--lake-parallel` / `--phase-*-timeout` defaults (resource budget belongs to the user).

Frequency discipline: even with authority, do not edit prompts faster than the pipeline can produce signal. Wait at least 30 commits or 1 hour after a prompt bump before another edit on the same file, unless the new prompt is producing immediate misbehaviour. Edit churn confuses codex.

Concrete autonomous-action examples this skill has handled:

- Removing chapters from `SCHEMA_ONLY_HORIZONS` once paper-side concrete instances landed (paper P699-P712 unlocked monoid/group/abgroup/ring/commring/field; updated `critical_path.py` constant + mirror in `phase_b.txt` BAN section without asking).
- Tightening `phase_d_lint.py` parameter-echo to be conclusion-aware after R1261/R1262 false positives.
- Splitting an oversized `.tex` file (now superseded by Makefile precheck — codex self-heals).

### Harness design principles

When the workflow keeps surfacing the same issue, the gate lives at the wrong level. Move it down. Levels of correctness enforcement, in preferred order:

1. **Build gate (Makefile precheck)** — the script that produces the artifact (PDF, lake build) refuses to run when an invariant breaks. Codex sees the failure in normal Step 2 and self-heals before commit. Generic, no theme-specific logic. Example: `papers/bedc/scripts/check_tex_size.sh` invoked by `Makefile`.
2. **Subprocess lint (hot-reloadable)** — `phase_d_lint.py`, `critical_path.py`, `bedc_ci.py audit --shape-saturation`. The orchestrator calls these via subprocess on each round, so edits take effect without restart. Use for mechanical pattern checks (regex on signatures, constraint-set membership, label uniqueness).
3. **Prompt HARD GATE (hot-reloaded)** — Phase B/C/Review/Revise prompts. Bumping `## Prompts version` mirrors into commit bodies for traceability. Use for guidance that needs codex's judgment but is articulable as a rule. Lower confidence than levels 1-2 because codex occasionally violates prompts.
4. **Long-running script body (restart-required)** — `codex_revise.py`, `codex_formalize.py` orchestrator body. Use for the merge flow itself, retry policy, gate ordering, default timeouts. Restart cost is the in-flight rounds drained.

When a gate fires unexpectedly (false positive), run it offline against the failed commit before tightening or relaxing it:

```bash
git -C /Users/chronoai/newmath worktree add /tmp/test <commit>
python3 lean4/scripts/phase_d_lint.py --worktree /tmp/test --base-branch <commit>^
git -C /Users/chronoai/newmath worktree remove /tmp/test
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
git -C /Users/chronoai/newmath log --oneline codex-auto-dev | head -20
python3 /Users/chronoai/newmath/lean4/scripts/bedc_ci.py audit
python3 /Users/chronoai/newmath/lean4/scripts/bedc_ci.py audit --shape-saturation
python3 /Users/chronoai/newmath/lean4/scripts/critical_path.py | jq '.top[:5]'
```

Merge:
```bash
ps -axo pid,etime,command | grep -E 'codex_revise|codex_formalize' | grep -v grep
git -C /Users/chronoai/newmath worktree list
git -C /Users/chronoai/newmath status --short  # MUST be empty while rounds are merging
```

Phase D dry-run on a worktree (predict what the lint will say without merging):
```bash
python3 /Users/chronoai/newmath/lean4/scripts/phase_d_lint.py \
  --worktree /Users/chronoai/newmath/.worktrees/round_R<N> \
  --base-branch codex-auto-dev
```

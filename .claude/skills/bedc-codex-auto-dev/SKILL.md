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
2. **Parameter-echo schema.** Signature contains `(name : ∀ … hsame …)` binding — i.e. a hypothesis quantifying over hsame as input. Used to be a Phase B/C HARD GATE that codex routinely ignored; moving the check to pipeline subprocess closes the loophole.
3. **BHist-anchor for Derived theorems.** Every new declaration under `BEDC.Derived.*` must mention at least one concrete BEDC kernel symbol (BHist / BMark / hsame / ProbeBundle / SigRel / NameCert / Pkg / e0 / e1 / cons / append / msame / Empty). Catches per-domain copies of the saturated shape family that don't anchor on `X`Up's concrete inductive.

Phase D failure routes through the same `(ok, gate_name, tail)` channel as audit failures and is not auto-recovered — the round is marked FAILED and the worktree is removed. To tighten any of the three regexes, edit `phase_d_lint.py` and the next round picks up the change.

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

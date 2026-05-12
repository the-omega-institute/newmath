# AI_GROWTH_MECHANISM

This document maps the current AI theory-growth machinery in BEDC and
identifies the optimisation surface where the pipeline self-evolves.
It is shared with the codex pipeline; every paper / lean round prompt
references it as part of REQUIRED FIRST STEP, alongside
`AI_THEORY_GROWTH_ROADMAP.md`.

## Goal

Operator wants:

1. **Every chapter must use the compiler formalisation** (not just
   ai-proposed ones). Hard quality control universally.
2. **AI writes code, AI evolves, AI fixes its own mistakes**, with
   the operator only intervening when AI doesn't know how to.
3. **Continuous unattended operation**. Daily status report.

The current pipeline gets us part of the way there. The gaps are
mapped below.

## Current AI growth pipeline (component map)

### A. Orchestrator processes (continuous background)

```
papers/bedc/scripts/codex_revise.py        paper round orchestrator
  - dispatches paper rounds (5 worker concurrency)
  - each round runs phase_review then phase_revise
  - merges round commit to codex-auto-dev
  - recovery queue for failed rounds

lean4/scripts/codex_formalize.py           lean round orchestrator
  - dispatches lean rounds (12 worker concurrency)
  - each round runs phase_b then phase_c
  - merges round commit to codex-auto-dev
  - recovery queue for failed rounds

tools/sync_with_auto_dev.py                sync daemon (every 600s)
  - bidirectional merge codex-auto-dev <-> auto-dev
  - codex-resolved conflicts
```

These are HOT processes. Restart loses in-flight worker state, so
operator constraint: do not restart unless absolutely necessary.

### B. Phase prompts (hot-reload, per-round behaviour)

```
papers/bedc/scripts/prompts/
  phase_review.txt       -- target selection (paper round step 1)
  phase_revise.txt       -- implementation (paper round step 2)
  phase_propose.txt      -- propose new ai chapter (manual trigger)
  conflict_resolve.txt   -- codex-side merge conflict resolver
  origin_sync_recover.txt
  post_rebase_audit_resolve.txt
  round_fallback_resolve.txt

lean4/scripts/prompts/
  phase_b.txt            -- target selection (lean round step 1)
  phase_c.txt            -- implementation (lean round step 2)
  conflict_resolve.txt
  origin_sync_recover.txt
  post_rebase_audit_resolve.txt
  round_fallback_resolve.txt
```

Prompts are read on every codex exec call. Edit a prompt, the next
round picks it up. This is the primary self-evolution surface: when
a recurring failure pattern appears in monitor logs, edit the prompt
to address the pattern, observe the next 2-3 rounds, iterate.

### C. Quality gates (run per round, machine-checkable)

```
cd lean4 && lake build                    # 0 sorry / valid Lean
tools/check-axioms.py                     # 0 axiom keyword
bedc_ci.py audit                          # paper-Lean drift
bedc_ci.py axiom-purity --strict          # 0 transitive axiom dep
bedc_ci.py conservativity-audit           # ai chapter no baseline leak
bedc_ci.py manifest-check                 # release-grade type-check
papers/bedc/Makefile precheck             # math env auto-rewrite
papers/bedc && make                       # PDF builds clean
```

Gates run as pre-merge hard gates inside each round's worktree. A
failure routes to the recovery queue, where codex retries with the
gate's error message as input. This is the primary error-recovery
loop: codex sees gate-fail, attempts fix, retries until pass or
unrecoverable.

### D. critical_path engine

```
lean4/scripts/critical_path.py            metadata/priority oracle
```

Reads:
- `papers/bedc/parts/**/*.tex` for closurestatus blocks, lean markers
- `lean4/BEDC/**/*.lean` for theorem inventory, `*Up_StdBridge` etc
- `papers/bedc/parts/visions/` for cross-cutting overlap analysis

Outputs (consumed by phase_review / phase_b prompts):
- `top[]`: priority chapters needing attention
- `top_transitions`: closure-grade rotation candidates
- `formal_axis_top`: chapters whose paper formal axis lags lean
- `bridge_candidates / drift_chapters / bridge_sync_pending`
- `closed_horizons / open_horizons` aggregate counts
- `capstone_overlap_map`

This is the *attention oracle*. It decides what codex looks at next.
The operator can edit `critical_path.py` to add new priority signals,
but the existing engine is feature-complete for the current pipeline.

### E. Operator-side review (manual)

```
lean4/scripts/review_proposals.py         proposal accept/reject CLI
papers/bedc/proposals/                    pending / accepted / rejected
```

Currently used only when the operator manually triggers
`phase_propose.txt`. Phase 2.5 (auto-trigger) is not yet wired into
the orchestrator (would require restart).

## Where AI writes code now

| Step | Codex action | Self-fixing? |
|------|--------------|--------------|
| phase_b target select | reads critical_path, picks 3 target lean theorems | dedup retry on conflict |
| phase_c implementation | writes new theorem proofs in lean | gate-fail → recovery queue → codex retry with gate error |
| phase_review target select | reads critical_path + roadmap, picks paper targets | dedup retry on chapter-lock |
| phase_revise implementation | writes paper edits | gate-fail → recovery |
| conflict_resolve | resolves merge conflicts | bounded retries |
| post_rebase_audit_resolve | drops colliding additions when audit fail | bounded retries |

So codex *does* already write code AND self-fix. The question is
whether the *prompts* themselves can be improved (= AI evolves the
framework, not just the content).

## Where AI does NOT yet evolve itself

```
1. Prompts are edited by the operator, not by codex.
2. critical_path.py is edited by the operator.
3. bedc_ci.py audit rules are edited by the operator.
4. Framework structure (TasteGate / NameCert / ChapterTasteGate)
   is edited by the operator.
```

For "AI evolves itself", these would have to become codex-editable
under operator review. Currently the operator is the bottleneck for
framework evolution.

Optimisation candidates (each is a future task):

1. **Prompt-evolution loop**: codex periodically scans monitor logs
   for recurring failure patterns and proposes a prompt patch via a
   `phase_meta_prompt.txt` mechanism. Operator approves the patch.
2. **Audit-rule evolution**: codex proposes new audit rules in
   `bedc_ci.py` when it detects a class of bypass that current rules
   don't catch (e.g. the cosmetic-vacuous-instance issue we caught
   manually).
3. **Critical-path signal evolution**: codex proposes new priority
   signals when it observes the existing ones aren't surfacing the
   right targets (e.g. content-axis vs closure-axis decoupling).

## Hard universal compiler-formalisation requirement

Operator wants every chapter — not just `\origin{ai}` — to use the
compiler formalisation. Currently:

- Baseline 280+ chapters: zero use of `event_flow_conservativity`,
  `flow_level_round_trip`, etc.
- TasteGate: only ai chapters, hard schema (Phase 3) since
  `1c7595fcd`.

Path to universal hard schema:

```
Step 1 (already done at 1c7595fcd): hard schema for ai chapters via
  ChapterTasteGate. Conservativity + no_hidden_input are derived from
  ground compiler theorems.

Step 2 (TODO): extend the audit gate so EVERY chapter (not just
  \origin=ai) past obligationClosure must cite a `BHistCarrier`
  instance and a `ChapterTasteGate` instance for its lean module.
  Baseline chapters that don't have one yet drop back from their
  current mature grade until they comply.

  Risk: this would force a one-time mass migration of 280+ chapters.
  Each chapter needs a real `toEventFlow` embedding, which for many
  chapters (Group / Hilbert / Curvature) is non-trivial design work.
  Feasibility: 1-2 months of pipeline time per ~30 chapters.

Step 3 (TODO): once Step 2 lands, the baseline / ai distinction
  shrinks to "did a human curate this name?" — both tracks share
  the same hard quality gate.
```

The operator's instruction is clear: do Step 2. The pipeline self-
implements Step 2 by:

1. paper round adds the BHistCarrier instance for one chapter at a
   time (via theory_extension target type, citing
   `BEDC.Meta.TasteGate.BHistCarrier`).
2. lean round implements the instance (via phase_c).
3. once all 280+ chapters have BHistCarrier instances, the audit
   gate is extended to require ChapterTasteGate.
4. chapters that don't yet have it drop back to scopedClosure until
   pipeline catches up. This is intentional — it forces the gate to
   be universally satisfied before any chapter claims maturity.

## Self-evolution loop design

The operator's request is: AI writes / evolves / fixes / reports
unattended. Concrete loop:

```
HOURLY (codex auto-runs):
  - paper round dispatches (every ~7-10 min, current rate)
  - lean round dispatches (every ~5-15 min)
  - sync daemon every 600s
  - audit / axiom-purity / conservativity run on every commit

DAILY (status report to operator):
  - aggregate: closed/open horizons, ai chapters count, gate fail
    rate, recovery success rate, critical_path top-3 chapters
  - flag: any chapter stuck in recovery > 12h, any prompt change
    that pipeline hasn't reflected
  - propose: 1-2 prompt edits or framework tweaks codex thinks would
    help; operator approves before they take effect

WEEKLY (architectural review):
  - check whether new chapters have integrated cleanly
  - check whether ai chapter count is growing (Phase 5 progress)
  - check whether universal hard schema (Step 2 above) progressed
  - propose 1-2 new chapters to seed manually if frontier saturated
```

Implementation: the daily report is generated by a script that runs
either via cloud cron (best, persists across sessions) or via the
operator's `crontab`. The contents come from `critical_path.py`'s
JSON output plus monitor log analysis.

## Codex-side instructions (read by phase prompts)

When you (codex) read this file:

1. The pipeline operates by you writing code in each round. Read
   gate-fail messages carefully when they appear — they are the
   pipeline's only feedback channel.
2. Every chapter eventually needs a `BHistCarrier` instance plus a
   `ChapterTasteGate` instance. When a target opportunity arises
   (chapter reaches obligationClosure) and the chapter lacks these,
   include them in your patch.
3. Conservativity and no-hidden-input are *derived theorems*; you
   don't have to prove them. Just supply `BHistCarrier` (with
   `toEventFlow` and `fromEventFlow`) and the two
   `ChapterTasteGate` fields (`round_trip` and `layer_separation`).
4. Always cite ground-compiler theorems when proving chapter-level
   claims about display recognisability. In particular:
   - For "every mark is b0/b1", use `event_flow_conservativity`.
   - For "Decode round-trips FlowEncoding", use
     `flow_level_round_trip` or `channel_bijection`.
   - For source/channel separation, use
     `source_channel_separation`.
5. If you (codex) notice a recurring failure pattern that the current
   prompts don't address, you may add a `\closureat` note to the
   chapter you're working on suggesting a prompt patch. The operator
   reads the daily report and decides whether to apply it.
